/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.CellProbe.OfWordRAM
public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Word-RAM Time-Space Lower Bounds for Dynamic Succinct Dictionaries

Contrapositive Word-RAM time-space trade-off lower bounds for dynamic succinct dictionaries
(`Dynamic.spec U V n`, supporting `insert`, `delete`, and `query`) from Li, Liang, Yu, and Zhou
([LiLiangYuZhou2023]; locators below follow `arXiv:2306.02253v3`, where printed page `p` is PDF
page `p + 1`), obtained by combining the multi-level step-indexed cell-probe lower bounds of
`CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound` with the zero-error
machine-to-cell-probe simulation bridges of `CslibFrontier.DataStructure.CellProbe.OfWordRAM`
([LiLiangYuZhou2023], Section 1, p. 1 footnote 1 / PDF p. 2, *"a cell-probe lower bound implies
the same time lower bound for RAM"*; [Yao1977]):

* **Primary headlines — actual expected Word-RAM running time (`expectedFlatTime_*`):**
  * **Theorem 1.1 / Theorem 3.1 (pp. 1, 10–13 / PDF pp. 2, 11–14):** `Ω(n * k)` actual expected
    Word-RAM body instructions (`ExecFlatProgramOps`) over `insertQueryDeleteDist` under
    `(((space + persCount input) * w : ℕ) : ℝ) ≤ benchmarkBits U V n +
    c_R * n * max (log^{(k)} n) 1` (`1 ≤ k ≤ log* n`), specializing at `k = Nat.logStar n`
    (`max (Nat.iterLog (Nat.logStar n) n) 1 = 1` for `2 ≤ n`) to `Ω(n * log* n)` under `O(n)` bits
    of redundancy.
  * **Theorem 1.2 / Theorem 6.1 and combined bound (pp. 2, 25–27 / PDF pp. 3, 26–28):**
    `Ω(n * log₂(n / max R 1))` actual expected Word-RAM body instructions for `R`-redundancy dynamic
    dictionaries (`R ≤ n`, vanishing at `R = n`), together with the combined
    `Ω(n * (log* n + max 0 (log₂(n / max R 1))))` bound across all `R ≤ c_R * n`.
  * **Theorem 1.3(1)–(2) and combined update-only bound (pp. 2, 27–30 / PDF pp. 3, 28–31):**
    update-only `Ω(n * k)`, `Ω(n * log₂(n / max R 1))`, and
    `Ω(n * (log* n + max 0 (log₂(n / max R 1))))` actual expected Word-RAM instruction lower bounds
    on `insertDeleteDist` for `3 * n ≤ U` and `U ^ (2 + α_V) ≤ V * n ^ 2`, with no query-time
    constraint.
* **Certified-budget corollaries (`expectedTotalCost_*`):** derived directly from the
  actual-expected-time flat-program headlines for any zero-error
  `WordRAM.Randomized.StateTransitionImpl` (including deterministic `WordRAM.StateTransitionImpl`s
  via `StateTransitionImpl.toRandomized`), lower-bounding `C.initPotential + E[totalCost C.charge]`
  ([CLRS2009], Section 17.3) under direct parameter-fit conditions on `(w, base, params, P)`.
* **Generic dictionary Word-RAM transfer bridges:** `expectedFlatTime_ge_of_indexedScheme`,
  `expectedFlatTime_update_ge_of_indexedScheme`, `expectedTotalCost_ge_of_indexedScheme`, and
  `expectedTotalCost_update_ge_of_indexedScheme`.

Formalization adaptations inherited from
`CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound` ([LiLiangYuZhou2023],
`arXiv:2306.02253v3`):
1. **Deterministic `c = 1` probe cap (`Sections 4.2, 5.1, 5.2, and 8.1`):** `arXiv:2306.02253v3`
   §4.2 (p. 14 / PDF p. 15) 1-indexes levels `ℓ ∈ {1, …, k}` with segment length `m_{ℓ-1}` and
   fanout `λ_ℓ`, so the `c = 1` cap reads `|S_A|, |S_B| ≤ m_{ℓ-1} * t` with Markov loss at most
   `(1 / 16) * λ_ℓ`. In `MetaTree`, internal parent nodes `(ℓ + 1, b)` for
   `ℓ ∈ {0, …, T.height - 1}` have child-segment length `m_ℓ = T.blockSize ℓ` and fanout
   `λ_{ℓ+1} = T.fanout (ℓ + 1)` (`T.blockSize (ℓ + 1) = T.blockSize ℓ * T.fanout (ℓ + 1)`), so
   `IsModeSeedConsistent` enforces `|S_A|, |S_B| ≤ m_ℓ * t` directly inside segment qualification
   (incurring at most `(1 / 16) * λ_{ℓ+1}` probe-cap probability loss via Markov's inequality on
   `nodeProbes` in `MetaTree.sum_prob_not_isGoodSeg_le`), preserving Claim 4.1 (`λ_{ℓ+1} / 4`) and
   Eq. (11) (`2(β + 1) m_ℓ t`) while keeping Step 5 separator messages deterministically bounded on
   `{W = 1}`.
2. **Internal Markov sub-conditioning in Step 6 (`Section 8.1`, Lemma 8.1):** sub-conditions on
   state-fiber multiplicity `c(T_B) ≤ 2 ^ (R + 1) * U ^ (γ * m)` over the uniform marginal of `T_B`
   (`Pr[bad] ≤ (1 / 2) * U ^ (-γ * m)`), costing `R + 2 + γ * m * log₂ U` bits in Step 6 while
   preserving Theorem 1.3's `U ^ (2 + α_V) ≤ V * n ^ 2` threshold.

Word-RAM model and boundary conventions:
* **Persistent state and constant-register overhead absorption ([LiLiangYuZhou2023], p. 1
  footnote 1):** a flat Word-RAM program `p_op : Program B r` with input mask `input : Fin r → Bool`
  maintains `space` memory words in `[base, base + space)` plus `persCount input` non-input
  registers (`input i = false`, coinciding with `persistentRegCount P` for `P : SubroutineCode`), so
  its persistent state across operation boundaries is `(space + persCount input) * w` bits
  (`space * w` bits when `∀ i, input i = true`). Simulating `p_op` in the cell-probe model adds
  `2 * persCount input` reload/spill probes per operation; because no zero-body-instruction program
  (`p_op[0]? = some (.halt _)`) can realize `Dynamic.spec U V n` for `1 ≤ n, 2 ≤ U, 1 ≤ V`, every
  operation executes at least `1` body instruction in expectation, absorbing the register spill term
  into the multiplicative factor `1 / (2 * persCount input + 1)` (hence into the constant `c > 0`
  for any fixed register budget `persCount input ≤ r_max`, with zero loss at `r_max = 0`).
* **Actual expected running time vs. certified resource budgets ([CLRS2009], Section 17.3):**
  `ExecFlatProgramOps.tighten_actualBodyTime` (in
  `CslibFrontier.DataStructure.CellProbe.OfWordRAM`) proves that **every** certified
  `ExecFlatProgramOps` execution with admissible budget `T_ops` also witnesses `ExecFlatProgramOps`
  at the exact intrinsic expected non-`halt` body-instruction count
  `flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops` (accumulating
  `expectedTime w p_op ⟨0, prepareFlatRegs input encode o x⟩ - 1` along `flatStateDist`, which on
  certified histories coincides with the exact limiting halting distribution at every operation
  boundary), preserving the coupled distributions `(ν₀, ν_final)` and zero-error correctness, with
  `flatExpectedBodyTime ... ops ≤ T_ops`. Total expected executed instructions including each
  operation's terminal `halt` satisfy
  `flatExpectedTime ... ops = flatExpectedBodyTime ... ops + ops.length`
  (`flatExpectedTime_eq_add_length`). All six `expectedFlatTime_*` headlines (and both generic
  `expectedFlatTime{,_update}_ge_of_indexedScheme` bridges) directly lower-bound
  `∑' ops, dist ops * flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops` with no
  caller-supplied budget `T` (including deterministic programs via `Latent := Unit`,
  `ν₀ := PMF.pure ((), x₀)`). The companion `expectedTotalCost_*` corollaries follow via
  `flatExpectedBodyTime_le` to lower-bound the certified potential-amortized budget
  `C.initPotential + E[totalCost C.charge]` of any `WordRAM.Randomized.StateTransitionImpl` (and
  deterministic `WordRAM.StateTransitionImpl`s via `StateTransitionImpl.toRandomized`).
* **Zero-error oblivious randomization and `R = n` boundary:** bounds apply to zero-error (Las
  Vegas) Word-RAM programs on oblivious sequences (`insertQueryDeleteDist` and `insertDeleteDist`);
  bounded-error (Monte Carlo) implementations and adaptive sequence adversaries are out of scope. At
  `R = n` (`n ≥ 1`), `log₂(n / max R 1) = 0`, where the `k = Nat.logStar n` and combined theorems
  supply the active lower bound.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.exists_flat_exec_of_stateTransitionImpl`:
  builds an initialized state distribution `ν₀` from a zero-error `StateTransitionImpl` together
  with exact `flatExpectedBodyTime` realization bounds `≤ C.initPotential + totalCost C.charge`.
* `Cslib.DataStructure.Dictionary.WordRAM.expectedFlatTime_ge_of_indexedScheme`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedFlatTime_update_ge_of_indexedScheme`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedTotalCost_ge_of_indexedScheme`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedTotalCost_update_ge_of_indexedScheme`:
  generic dictionary cell-probe-to-Word-RAM lower-bound transfer bridges.
* `Cslib.DataStructure.Dictionary.WordRAM.expectedFlatTime_ge_of_iterLog_redundancy`:
  Word-RAM Theorem 1.1 / Theorem 3.1 (`Ω(n * k)` actual expected running time, specializing at
  `k = Nat.logStar n` to `Ω(n * log* n)`).
* `Cslib.DataStructure.Dictionary.WordRAM.expectedFlatTime_ge_of_sublinear_redundancy`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedFlatTime_ge_iterLogStar_add_log_div`:
  Word-RAM Theorem 1.2 / Theorem 6.1 and combined `Ω(n * (log* n + max 0 (log₂(n / max R 1))))`
  actual expected running-time lower bounds.
* `Cslib.DataStructure.Dictionary.WordRAM.expectedFlatTime_update_ge_iterLog`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedFlatTime_update_ge_sublinear`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedFlatTime_update_ge_iterLogStar_add_log_div`:
  Word-RAM Theorem 1.3(1)–(2) and combined update-only actual expected running-time lower bounds.
* `Cslib.DataStructure.Dictionary.WordRAM.expectedTotalCost_ge_of_iterLog_redundancy`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedTotalCost_ge_of_sublinear_redundancy`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedTotalCost_ge_iterLogStar_add_log_div`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedTotalCost_update_ge_iterLog`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedTotalCost_update_ge_sublinear`,
  `Cslib.DataStructure.Dictionary.WordRAM.expectedTotalCost_update_ge_iterLogStar_add_log_div`:
  certified potential-amortized budget corollaries for `WordRAM.Randomized.StateTransitionImpl`.

## References

* [T. Li, J. Liang, H. Yu and R. Zhou, *Tight Cell-Probe Lower Bounds for Dynamic Succinct
  Dictionaries*][LiLiangYuZhou2023], Sections 1, 3, 4.2, 5.1, 5.2, 6, 7, and 8
  (`arXiv:2306.02253v3`).
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 17.3][CLRS2009]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM

open Cslib.WordRAM Cslib.CellProbe Cslib.DataStructure
open Cslib.DataStructure.CellProbe Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.CellProbe
open Cslib.Probability
open scoped BigOperators ENNReal

universe z

/-! ### 1. Positive body-instruction lower bounds, initial-data construction, and `ℝ≥0∞` helpers -/

private theorem execProgramDist_halt0_eq_pure {B : Basis} {r w : ℕ} {p : Program B r}
    {retReg : Fin r} (hp0 : p[0]? = some (.halt retReg)) (x : Data r)
    {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞}
    (h : ExecProgramDist w p x μ T) :
    μ = PMF.pure (x.regs retReg, x) := by
  have h1 : evalRand w p 1 ⟨0, x⟩ = PMF.pure (.halted (x.regs retReg) x) := by
    simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
    rw [stepRand_halt (s := ⟨0, x⟩) (i := retReg) hp0, ProbComp.eval_pure]
  have h2 : ∀ t ≥ 1, evalRand w p t ⟨0, x⟩ = PMF.pure (.halted (x.regs retReg) x) := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    induction d with
    | zero => exact h1
    | succ d ih =>
      rw [← Nat.add_assoc, evalRand, runRand_add w p (1 + d) 1, ProbComp.eval_bind]
      change (evalRand w p (1 + d) ⟨0, x⟩).bind _ = _
      rw [ih (Nat.le_add_right 1 d), PMF.pure_bind]
      simp [runRand_succ, runRand_zero, stepRand_halted]
  ext ⟨v, y⟩
  rw [← h.haltedLim_eq (v, y)]
  dsimp only [haltedLim]
  by_cases hvy : (v, y) = (x.regs retReg, x)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hvy.symm
    rw [PMF.pure_apply_self]
    refine le_antisymm (iSup_le fun t => ?_) ?_
    · by_cases ht : 1 ≤ t
      · rw [h2 t ht, PMF.pure_apply_self]
      · simp [Nat.eq_zero_of_not_pos ht, evalRand, runRand_zero]
    · calc (1 : ℝ≥0∞)
        _ = (evalRand w p 1 ⟨0, x⟩) (.halted (x.regs retReg) x) := by
            rw [h1, PMF.pure_apply_self]
        _ ≤ ⨆ t, (evalRand w p t ⟨0, x⟩) (.halted (x.regs retReg) x) :=
            le_iSup (fun t => (evalRand w p t ⟨0, x⟩) (.halted (x.regs retReg) x)) 1
  · rw [PMF.pure_apply_of_ne _ _ hvy]
    refine le_antisymm (iSup_le fun t => ?_) zero_le
    by_cases ht : 1 ≤ t
    · rw [h2 t ht]
      exact (PMF.pure_apply_of_ne _ _ (mt (Prod.ext_iff.mpr ∘ RandCfg.halted.inj) hvy)).le
    · simp [Nat.eq_zero_of_not_pos ht, evalRand, runRand_zero]

private theorem execFlatProgramOps_cons_inv
    {B : Basis} {r w base space : ℕ} {D : StateTransitionSpec.{0, 0, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} {p_op : Program B r} {input : Fin r → Bool}
    {encode : D.Op → Fin r → ℕ}
    {decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)}
    {s : D.State} {o : D.Op} {ops : List D.Op}
    {ν ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞}
    (hex : ExecFlatProgramOps D Latent w base space p_op input encode decode s (o :: ops)
      ν ν_final T_ops) :
    ∃ (μ_step : Latent × Data r → PMF (Latent × ℕ × Data r))
      (T_step : Latent × Data r → ℝ≥0∞) (T_rest : ℝ≥0∞),
      (∀ p ∈ ν.support,
        (∀ i, input i = true → Fits w (encode o i)) ∧
        ExecProgramDist w p_op (prepareFlatRegs input encode o p.2)
          ((μ_step p).map Prod.snd) (T_step p + 1) ∧
        ∀ q ∈ (μ_step p).support,
          q.2.2.Bounded w ∧
          decode o q.2.1 q.2.2.regs = some (D.stepFn s o).2 ∧
          Modifies (Block.mk base space).footprint p.2.mem q.2.2.mem) ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode (D.stepFn s o).1 ops
        (ν.bind fun p => (μ_step p).map fun q => (q.1, q.2.2)) ν_final T_rest := by
  generalize hops' : (o :: ops) = ops_idx at hex
  induction hex with
  | nil => cases hops'
  | cons hstep hrem _ =>
    cases hops'
    exact ⟨_, _, _, fun p hp =>
      ⟨(hstep p hp).1, (hstep p hp).2.1, fun q hq => (hstep p hp).2.2 q.1 q.2.1 q.2.2 hq⟩, hrem⟩

private theorem decode_after_halt0_two_steps
    {B : Basis} {U V n r w base space : ℕ} {Latent : Type z}
    {p_op : Program B r} {retReg : Fin r} (hp0 : p_op[0]? = some (.halt retReg))
    {input : Fin r → Bool}
    {encode : Dynamic.Op U → Fin r → ℕ}
    {decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result}
    {ν₀ ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞}
    {p₀ : Latent × Data r} (hp₀ : p₀ ∈ ν₀.support)
    (o₁ : Dynamic.Op U) (u_q : Fin U)
    (hex : ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
      (Dictionary.empty U) [o₁, .query u_q] ν₀ ν_final T_ops) :
    let x_q := prepareFlatRegs input encode (.query u_q) (prepareFlatRegs input encode o₁ p₀.2)
    decode (.query u_q) (x_q.regs retReg) x_q.regs =
      some ((Dynamic.step (Dynamic.step (Dictionary.empty U) o₁).1 (.query u_q)).2) := by
  dsimp only
  obtain ⟨μ₁, _, _, hstep₁, hrem₁⟩ := execFlatProgramOps_cons_inv hex
  obtain ⟨q₁, hq₁⟩ := (μ₁ p₀).support_nonempty
  have hq₁_eq : q₁.2 = (_, prepareFlatRegs input encode o₁ p₀.2) :=
    (PMF.mem_support_pure_iff _ _).mp
      (execProgramDist_halt0_eq_pure hp0 _ (hstep₁ p₀ hp₀).2.1 ▸
        (PMF.mem_support_map_iff _ _ _).mpr ⟨q₁, hq₁, rfl⟩)
  have hmem_b₁ : (q₁.1, q₁.2.2) ∈ (ν₀.bind fun p => (μ₁ p).map fun q => (q.1, q.2.2)).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨p₀, hp₀, (PMF.mem_support_map_iff _ _ _).mpr ⟨q₁, hq₁, rfl⟩⟩
  obtain ⟨μ₂, _, _, hstep₂, _⟩ := execFlatProgramOps_cons_inv hrem₁
  obtain ⟨q₂, hq₂⟩ := (μ₂ (q₁.1, q₁.2.2)).support_nonempty
  have hq₂_eq : q₂.2 = (_, prepareFlatRegs input encode (.query u_q) q₁.2.2) :=
    (PMF.mem_support_pure_iff _ _).mp
      (execProgramDist_halt0_eq_pure hp0 _ (hstep₂ _ hmem_b₁).2.1 ▸
        (PMF.mem_support_map_iff _ _ _).mpr ⟨q₂, hq₂, rfl⟩)
  have hd := ((hstep₂ _ hmem_b₁).2.2 q₂ hq₂).2.1
  rwa [congrArg Prod.fst hq₂_eq, congrArg Prod.snd hq₂_eq, congrArg Prod.snd hq₁_eq] at hd

private theorem not_halt_zero_of_execFlatProgramOps
    {B : Basis} {U V n M r w base space : ℕ} {Latent : Type z}
    (hn : 1 ≤ n) (hU : 2 ≤ U) (hV : 1 ≤ V) (hM : 2 ≤ M)
    {p_op : Program B r} {input : Fin r → Bool}
    {encode : Dynamic.Op U → Fin r → ℕ}
    {decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result}
    (ν₀ : PMF (Latent × Data r))
    (hex_corr : ∀ ops ∈ validHistoriesUpTo U V n M, ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
      ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
        (Dictionary.empty U) ops ν₀ ν_final T_ops)
    (retReg : Fin r) :
    p_op[0]? ≠ some (.halt retReg) := by
  intro hp0
  obtain ⟨p₀, hp₀⟩ := ν₀.support_nonempty
  let u₀ : Fin U := ⟨0, by omega⟩
  let u₁ : Fin U := ⟨1, by omega⟩
  have hv : ∀ u : Fin U, [Dynamic.Op.insert u 0, .query u₀] ∈ validHistoriesUpTo U V n M :=
    fun _ => ⟨by
      dsimp only [Dynamic.spec, StateTransitionSpec.ValidHistory, StateTransitionSpec.ofFn,
        Dynamic.valid]
      exact ⟨⟨Or.inl (by simp; omega), by omega⟩, trivial, trivial⟩, by simp; omega⟩
  obtain ⟨_, _, _, hex₀⟩ := hex_corr _ (hv u₀)
  obtain ⟨_, _, _, hex₁⟩ := hex_corr _ (hv u₁)
  have hans₀ := decode_after_halt0_two_steps hp0 hp₀ (.insert u₀ 0) u₀ hex₀
  have hans₁ := decode_after_halt0_two_steps hp0 hp₀ (.insert u₁ 0) u₀ hex₁
  have hregs_eq :
      (prepareFlatRegs input encode (.query u₀)
          (prepareFlatRegs input encode (.insert u₀ 0) p₀.2)).regs =
        (prepareFlatRegs input encode (.query u₀)
          (prepareFlatRegs input encode (.insert u₁ 0) p₀.2)).regs :=
    funext fun i => by by_cases hi : input i = true <;> simp [prepareFlatRegs, hi]
  have hne_u : u₀ ≠ u₁ := by simp [u₀, u₁]
  simp only [Dictionary.empty, Function.update_self, Function.update_of_ne hne_u, hregs_eq]
    at hans₀ hans₁
  cases hans₀.symm.trans hans₁

private theorem one_le_of_execProgramDist_no_halt0
    {B : Basis} {r w : ℕ} {p : Program B r}
    (hno : ∀ retReg : Fin r, p[0]? ≠ some (.halt retReg))
    {x : Data r} {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞}
    (hp : ExecProgramDist w p x μ (T + 1)) :
    (1 : ℝ≥0∞) ≤ T := by
  have h0 : (evalRand w p 0 ⟨0, x⟩).toOuterMeasure {cfg | ∃ u, cfg = .running u} = 1 := by
    simp [evalRand, runRand_zero, PMF.toOuterMeasure_pure_apply]
  have hhalt1 : (evalRand w p 1 ⟨0, x⟩).toOuterMeasure (RandCfg.haltedSet r) = 0 := by
    simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro cfg' hmem_s hmem_halt
    rw [ProbComp.support_eval] at hmem_s
    obtain ⟨_, _, rfl⟩ := hmem_halt
    by_cases hrand : ∃ dst src, p[0]? = some (.rand dst src)
    · obtain ⟨dst, src, hp0⟩ := hrand
      by_cases hfit : Fits w (x.regs src)
      · rw [stepRand_rand_of_fits (s := ⟨0, x⟩) hp0 hfit] at hmem_s
        obtain ⟨_, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hmem_s
        cases OracleComp.eq_of_mem_supportWith_pure hk
      · rw [stepRand_rand_of_not_fits (s := ⟨0, x⟩) hp0 hfit] at hmem_s
        cases OracleComp.eq_of_mem_supportWith_pure hmem_s
    · rw [stepRand_eq_ofOutcome_of_ne_rand (s := ⟨0, x⟩) fun dst src h => hrand ⟨dst, src, h⟩]
        at hmem_s
      have heq := OracleComp.eq_of_mem_supportWith_pure hmem_s
      cases hs_step : WordRAM.step w p ⟨0, x⟩ with
      | next _ => rw [hs_step] at heq; cases heq
      | fault => rw [hs_step] at heq; cases heq
      | halt _ =>
        rcases hp0 : p[0]? with _ | (_ | _ | _ | i | _)
        · simp [WordRAM.step, hp0] at hs_step
        · simp only [WordRAM.step, hp0] at hs_step
          split at hs_step <;> cases hs_step
        all_goals first | exact hno _ hp0 | simp [WordRAM.step, hp0] at hs_step
  have h1 : (evalRand w p 1 ⟨0, x⟩).toOuterMeasure {cfg | ∃ u, cfg = .running u} = 1 := by
    have hpart := hp.2.1.running_add_halted_eq_one 1
    rwa [hhalt1, add_zero] at hpart
  have h2 : (1 : ℝ≥0∞) + 1 ≤ T + 1 := by
    calc (1 : ℝ≥0∞) + 1
      _ = ∑ t ∈ Finset.range 2,
            (evalRand w p t ⟨0, x⟩).toOuterMeasure {cfg | ∃ u, cfg = .running u} := by
          rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
      _ ≤ expectedTime w p ⟨0, x⟩ := sum_le_tsum (Finset.range 2)
      _ ≤ T + 1 := hp.1
  exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp h2

private theorem length_le_execFlatProgramOps
    {B : Basis} {r w base space : ℕ} {D : StateTransitionSpec.{0, 0, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} {p_op : Program B r} {input : Fin r → Bool}
    {encode : D.Op → Fin r → ℕ}
    {decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)}
    (hno : ∀ retReg : Fin r, p_op[0]? ≠ some (.halt retReg))
    {s : D.State} {ops : List D.Op} {ν ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞}
    (hex : ExecFlatProgramOps D Latent w base space p_op input encode decode s ops ν ν_final
      T_ops) :
    (ops.length : ℝ≥0∞) ≤ T_ops := by
  induction hex with
  | nil => simp
  | @cons _ _ ops_rem ν_cur _ _ T_step T_rest hstep _ ih =>
    have hstep_ge : (1 : ℝ≥0∞) ≤ ∑' p, ν_cur p * T_step p := by
      calc (1 : ℝ≥0∞)
        _ = ∑' p, ν_cur p * (1 : ℝ≥0∞) := by simp [ν_cur.tsum_coe]
        _ ≤ ∑' p, ν_cur p * T_step p :=
            Cslib.Probability.PMF.tsum_mul_mono_support ν_cur fun p hp =>
              one_le_of_execProgramDist_no_halt0 hno (hstep p hp).2.1
    rw [List.length_cons, Nat.cast_succ, add_comm]
    exact add_le_add hstep_ge ih

private theorem code_size_pos {B : Basis} {r : ℕ} (c : Code B r) : 1 ≤ c.size := by
  induction c <;> simp only [Code.size] <;> omega

private theorem code_assemble_zero_ne_halt {B : Basis} {r : ℕ} (c : Code B r) (pc : ℕ)
    (retReg : Fin r) :
    (c.assemble pc)[0]? ≠ some (.halt retReg) := by
  induction c generalizing pc with
  | seq c₁ c₂ ih₁ _ =>
    simp only [Code.assemble, List.getElem?_append_left (c₁.length_assemble pc ▸ code_size_pos c₁)]
    exact ih₁ pc
  | _ => simp [Code.assemble]

private theorem code_program_zero_ne_halt {B : Basis} {r : ℕ} (c : Code B r) (out retReg : Fin r) :
    (c.program out)[0]? ≠ some (.halt retReg) := by
  simp only [Code.program, List.getElem?_append_left (c.length_assemble 0 ▸ code_size_pos c)]
  exact code_assemble_zero_ne_halt c 0 retReg

private theorem exists_initData_of_fits {B : Basis} {r_ds k_init w base : ℕ}
    (P : SubroutineCode B r_ds k_init) {params : Fin k_init → ℕ}
    (hbase : Fits w base)
    (hparams_fit : ∀ j, Fits w (params j))
    (hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
    (hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j) :
    ∃ d₀ : Data r_ds,
      d₀.Bounded w ∧
      d₀.regs P.frontierReg = base ∧
      (∀ j, d₀.regs (P.initParams j) = params j) ∧
      ∀ a, d₀.mem a = 0 := by
  classical
  refine ⟨{ regs := fun i =>
              if i = P.frontierReg then base
              else if h : ∃ j, P.initParams j = i then params (Classical.choose h)
              else 0
            mem := fun _ => 0 },
    ⟨fun i => ?_, fun _ => fits_zero w⟩, by simp, fun j => ?_, fun _ => rfl⟩
  · dsimp only
    split_ifs with h₁ h₂
    exacts [hbase, hparams_fit (Classical.choose h₂), fits_zero w]
  · dsimp only
    split_ifs with h₁ h₂
    exacts [(hparams_fr j h₁).symm, hparams_agree _ j (Classical.choose_spec h₂),
      absurd ⟨j, rfl⟩ h₂]

/-- Extract an initialized latent-state distribution `ν₀` from any zero-error
`WordRAM.Randomized.StateTransitionImpl`, witnessing `ExecFlatProgramOps` along every valid
dictionary history at its exact intrinsic expected non-`halt` body-instruction count
`flatExpectedBodyTime w (P.code.program P.output) P.input C.encode (ν₀.map Prod.snd) ops`
bounded by `C.initPotential + totalCost C.charge`. Delegates initialization and amortization to
`StateTransitionImpl.exists_init_and_flat_steps` and tightens to the exact count via
`ExecFlatProgramOps.tighten_actualBodyTime`. -/
theorem exists_flat_exec_of_stateTransitionImpl
    {B : Basis} {U V n r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
    (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base params
      (Dictionary.empty U))
    (hbase : Fits w base)
    (hparams_fit : ∀ j, Fits w (params j))
    (hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
    (hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j) :
    ∃ ν₀ : PMF (C.Seed × Data r_ds),
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧ ∀ a ∉ (Block.mk base C.space).footprint, p.2.mem a = 0) ∧
      ∀ ops, (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) ops →
        let T_act := flatExpectedBodyTime w (P.code.program P.output) P.input C.encode
          (ν₀.map Prod.snd) ops
        T_act ≤ (C.initPotential : ℝ≥0∞) +
          ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) ∧
        T_act ≠ ⊤ ∧
        ∃ ν_final,
          ExecFlatProgramOps (Dynamic.spec U V n) C.Seed w base C.space
            (P.code.program P.output) P.input C.encode (fun o _ regs => C.decode o regs)
            (Dictionary.empty U) ops ν₀ ν_final T_act := by
  obtain ⟨d₀, hd₀, hfr, hpar, _⟩ :=
    exists_initData_of_fits P hbase hparams_fit hparams_fr hparams_agree
  obtain ⟨ν₀, hsupp₀, hsteps⟩ := C.exists_init_and_flat_steps hd₀ hfr hpar
  refine ⟨ν₀, hsupp₀, fun ops hv => ?_⟩
  obtain ⟨ν_final, T_ops, hT_le, hT_fin, hex⟩ := hsteps ops hv
  obtain ⟨hex_act, hact_le, _⟩ := hex.tighten_actualBodyTime
  exact ⟨hact_le.trans hT_le, ne_top_of_le_ne_top hT_fin hact_le, ν_final, hex_act⟩

private theorem le_initPotential_add_tsum_totalCost
    {U V n : ℕ} (dist : PMF (List (Dynamic.Op U)))
    (initPotential : ℕ) (charge : Dictionary.State U → Dynamic.Op U → ℕ)
    {T : List (Dynamic.Op U) → ℝ≥0∞} {LB : ℝ≥0∞}
    (hlb : LB ≤ ∑' ops, dist ops * T ops)
    (hT : ∀ ops ∈ dist.support,
      T ops ≤ (initPotential : ℝ≥0∞) +
        ((Dynamic.spec U V n).totalCost charge (Dictionary.empty U) ops : ℝ≥0∞)) :
    LB ≤ (initPotential : ℝ≥0∞) +
      ∑' ops, dist ops *
        ((Dynamic.spec U V n).totalCost charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  exact hlb.trans ((Cslib.Probability.PMF.tsum_mul_mono_support dist hT).trans_eq
    (Cslib.Probability.PMF.tsum_mul_add_of_support dist
      (g := fun _ => (initPotential : ℝ≥0∞))
      (f := fun ops => ((Dynamic.spec U V n).totalCost charge (Dictionary.empty U) ops : ℝ≥0∞))
      fun _ _ => rfl))

private theorem tsum_mul_add_const_length {Op : Type*} (dist : PMF (List Op))
    (cost : List Op → ℝ≥0∞) (ov : ℝ≥0∞) {L : ℕ}
    (hlen : ∀ {ops}, ops ∈ dist.support → ops.length = L) :
    (∑' ops, dist ops * (cost ops + ov * (ops.length : ℝ≥0∞))) =
      (∑' ops, dist ops * cost ops) + ov * (L : ℝ≥0∞) := by
  have hswap := Cslib.Probability.PMF.tsum_mul_congr_support dist
    (f := fun ops => cost ops + ov * (ops.length : ℝ≥0∞))
    (g := fun ops => ov * (ops.length : ℝ≥0∞) + cost ops)
    (fun ops _ => add_comm _ _)
  have hadd := Cslib.Probability.PMF.tsum_mul_add_of_support dist
    (g := fun ops => ov * (ops.length : ℝ≥0∞)) (f := cost)
    (c := ov * (L : ℝ≥0∞)) (fun ops hops => by rw [hlen hops])
  exact hswap.trans (hadd.trans (add_comm _ _))

private theorem const_le_tsum_of_support {Op : Type*} (dist : PMF (List Op))
    (cost : List Op → ℝ≥0∞) {L : ℝ≥0∞}
    (hle : ∀ {ops}, ops ∈ dist.support → L ≤ cost ops) :
    L ≤ ∑' ops, dist ops * cost ops :=
  (show L = ∑' ops, dist ops * L by rw [ENNReal.tsum_mul_right, dist.tsum_coe, one_mul]).trans_le
    (Cslib.Probability.PMF.tsum_mul_mono_support dist fun _ hops => hle hops)

private theorem ofReal_div_pers_le_of_le_add_mul {B : ℝ} {p L : ℕ} {T : ℝ≥0∞}
    (hL : (L : ℝ≥0∞) ≤ T)
    (hB : ENNReal.ofReal B ≤ T + ((2 * p : ℕ) : ℝ≥0∞) * (L : ℝ≥0∞)) :
    ENNReal.ofReal (B / (2 * (p : ℝ) + 1)) ≤ T := by
  have hden : ENNReal.ofReal (2 * (p : ℝ) + 1) = ((2 * p + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast ENNReal.ofReal_natCast (2 * p + 1)
  rw [ENNReal.ofReal_div_of_pos (by positivity), hden]
  refine ENNReal.div_le_of_le_mul (hB.trans ?_)
  calc T + ((2 * p : ℕ) : ℝ≥0∞) * (L : ℝ≥0∞)
    _ ≤ T + ((2 * p : ℕ) : ℝ≥0∞) * T := add_le_add le_rfl (mul_le_mul' le_rfl hL)
    _ = T * ((2 * p + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring

/-! ### 2. Generic Dictionary Cell-Probe-to-Word-RAM Lower-Bound Transfer Bridges -/

private theorem modeHorizon_false (n : ℕ) : modeHorizon false n = 3 * n := by
  simp only [modeHorizon, modeStride, Bool.false_eq_true, ↓reduceIte]
  ring

private theorem modeHorizon_true (n : ℕ) : modeHorizon true n = 4 * n := by
  simp only [modeHorizon, modeStride, ↓reduceIte]
  ring

private theorem modeDist_support_spec (withQueries : Bool) {U V n : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) :
    ∀ {ops}, ops ∈ (modeDist withQueries U V n hU hV).support →
      (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) ops ∧
        ops.length = modeHorizon withQueries n ∧
        ∀ o ∈ ops, o ∈ validOps U V := by
  intro ops hops
  cases withQueries
  · rw [modeDist_false] at hops
    obtain ⟨hv, halph⟩ := validHistory_of_mem_support_insertDeleteDist hops
    exact ⟨hv, (length_of_mem_support_insertDeleteDist hops).trans (modeHorizon_false n).symm,
      halph⟩
  · rw [modeDist_true] at hops
    obtain ⟨hv, halph⟩ := validHistory_of_mem_support_insertQueryDeleteDist hops
    exact ⟨hv, (length_of_mem_support_insertQueryDeleteDist hops).trans (modeHorizon_true n).symm,
      halph⟩

private theorem totalCost_ge_of_flat_fn
    {B : Basis} {U V n M r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
    (dist : PMF (List (Dynamic.Op U)))
    (hdist : ∀ ops ∈ dist.support, (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) ops)
    (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base params
      (Dictionary.empty U))
    (hbase : Fits w base)
    (hparams_fit : ∀ j, Fits w (params j))
    (hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
    (hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j)
    {LB : ℝ≥0∞}
    (hflat : ∀ (ν₀ : PMF (C.Seed × Data r_ds)),
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧ ∀ a ∉ (Block.mk base C.space).footprint, p.2.mem a = 0) →
      (∀ ops ∈ validHistoriesUpTo U V n M, ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) C.Seed w base C.space (P.code.program P.output)
          P.input C.encode (fun o _ regs => C.decode o regs) (Dictionary.empty U) ops ν₀ ν_final
          T_ops) →
      LB ≤ ∑' ops, dist ops *
        flatExpectedBodyTime w (P.code.program P.output) P.input C.encode
          (ν₀.map Prod.snd) ops) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, dist ops *
        ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨ν₀, hsupp₀, hsteps⟩ :=
    exists_flat_exec_of_stateTransitionImpl C hbase hparams_fit hparams_fr hparams_agree
  exact le_initPotential_add_tsum_totalCost dist C.initPotential C.charge
    (hflat ν₀ hsupp₀ fun ops hops =>
      let ⟨_, hfin, ν_f, hex⟩ := hsteps ops hops.1
      ⟨ν_f, _, hfin, hex⟩)
    fun ops hops => (hsteps ops (hdist ops hops)).1

private theorem le_expectedFlatTime_mode_of_no_halt (withQueries : Bool)
    {B : Basis} {U V n r w base space S_max : ℕ} {input : Fin r → Bool} {Latent : Type z}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (hspace : space + persCount input ≤ S_max)
    (p_op : Program B r)
    (hno : ∀ retReg, p_op[0]? ≠ some (.halt retReg))
    (encode : Dynamic.Op U → Fin r → ℕ)
    (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
          (Dictionary.empty U) ops ν₀ ν_final T_ops)
    {LB : ℝ}
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result S_max w},
      (∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      LB ≤ ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (LB / (2 * (persCount input : ℝ) + 1)) ≤
      ∑' ops, modeDist withQueries U V n hU hV ops *
        flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  let dist := modeDist withQueries U V n hU hV
  let L := modeHorizon withQueries n
  let bodyTime : List (Dynamic.Op U) → ℝ≥0∞ :=
    flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd)
  have hex_hard : ∀ ops ∈ dist.support, ∃ ν_final T_ops,
      T_ops ≤ bodyTime ops ∧ T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
          (Dictionary.empty U) ops ν₀ ν_final T_ops := fun ops hops => by
    obtain ⟨hv, hlen, _⟩ := modeDist_support_spec withQueries hU hV hops
    obtain ⟨ν_final, T_ops, hfin, hex⟩ :=
      hex_corr ops ⟨hv, hlen.trans_le (Nat.le_succ L)⟩
    obtain ⟨hex_act, hact_le, _⟩ := hex.tighten_actualBodyTime
    exact ⟨ν_final, bodyTime ops, le_rfl, ne_top_of_le_ne_top hfin hact_le, hex_act⟩
  have hraw := flat_wordRAM_lower_bound_of_det_cellProbe (D := Dynamic.spec U V n)
    (Dictionary.empty U) hspace p_op encode
    decode ν₀ hsupp₀ (validOps U V) (L + 1) (validHistoriesUpTo U V n (L + 1))
    (fun _ hops => validHistoriesUpTo_spec hops) hex_corr dist
    (fun ops hops => by
      obtain ⟨hv, hlen, halph⟩ := modeDist_support_spec withQueries hU hV hops
      exact ⟨hv, hlen.trans_le (Nat.le_succ L), halph⟩)
    bodyTime hex_hard fun D_det hD =>
      ofReal_le_tsum_seqProbes_of_toReal_le dist D_det (hlb hD)
  rw [tsum_mul_add_const_length dist bodyTime _
    fun hops => (modeDist_support_spec withQueries hU hV hops).2.1] at hraw
  have hL_le : (L : ℝ≥0∞) ≤ ∑' ops, dist ops * bodyTime ops :=
    const_le_tsum_of_support dist bodyTime fun {ops} hops => by
      obtain ⟨_, T_ops, hT_le, _, hex⟩ := hex_hard ops hops
      have hlen_eq := (modeDist_support_spec withQueries hU hV hops).2.1
      exact (hlen_eq ▸ length_le_execFlatProgramOps hno hex).trans hT_le
  exact ofReal_div_pers_le_of_le_add_mul hL_le hraw

private theorem le_expectedFlatTime_mode_of_det_indexedScheme (withQueries : Bool)
    {B : Basis} {U V n r w base space S_max : ℕ} {input : Fin r → Bool} {Latent : Type z}
    (hn : 1 ≤ n) (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (hspace : space + persCount input ≤ S_max)
    (p_op : Program B r)
    (encode : Dynamic.Op U → Fin r → ℕ)
    (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
          (Dictionary.empty U) ops ν₀ ν_final T_ops)
    {LB : ℝ}
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result S_max w},
      (∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      LB ≤ ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (LB / (2 * (persCount input : ℝ) + 1)) ≤
      ∑' ops, modeDist withQueries U V n hU hV ops *
        flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  have hM2 : 2 ≤ modeHorizon withQueries n + 1 := by
    cases withQueries <;> simp only [modeHorizon_false, modeHorizon_true] <;> omega
  exact le_expectedFlatTime_mode_of_no_halt withQueries hU hV hspace p_op
    (not_halt_zero_of_execFlatProgramOps hn (by omega) hV hM2 ν₀ hex_corr)
    encode decode ν₀ hsupp₀ hex_corr hlb

private theorem le_expectedTotalCost_mode_of_det_indexedScheme (withQueries : Bool)
    {B : Basis} {U V n r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base params
      (Dictionary.empty U))
    (hbase : Fits w base)
    (hparams_fit : ∀ j, Fits w (params j))
    (hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
    (hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    {LB : ℝ}
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result S_max w},
      (∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      LB ≤ ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (LB / (2 * (persistentRegCount P : ℝ) + 1)) ≤
      (C.initPotential : ℝ≥0∞) +
        ∑' ops, modeDist withQueries U V n hU hV ops *
          ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  rw [persistentRegCount_eq_persCount] at hspace ⊢
  exact totalCost_ge_of_flat_fn (M := modeHorizon withQueries n + 1)
    (modeDist withQueries U V n hU hV)
    (fun _ hops => (modeDist_support_spec withQueries hU hV hops).1)
    C hbase hparams_fit hparams_fr hparams_agree fun ν₀ hsupp₀ hex_corr =>
      le_expectedFlatTime_mode_of_no_halt withQueries hU hV hspace (P.code.program P.output)
        (code_program_zero_ne_halt P.code P.output) C.encode (fun o _ regs => C.decode o regs)
        ν₀ hsupp₀ hex_corr hlb

/-- Transfer any deterministic step-indexed `IndexedScheme` lower bound over
`insertQueryDeleteDist` directly to the exact intrinsic expected non-`halt` body-instruction count
`flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops` (hence also to total executed
instructions `flatExpectedTime = flatExpectedBodyTime + ops.length` and to any admissible
`ExecFlatProgramOps` budget `T_ops` via `ExecFlatProgramOps.flatExpectedBodyTime_le`). -/
theorem expectedFlatTime_ge_of_indexedScheme
    {B : Basis} {U V n r w base space S_max : ℕ} {input : Fin r → Bool} {Latent : Type z}
    (hn : 1 ≤ n) (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (hspace : space + persCount input ≤ S_max)
    (p_op : Program B r)
    (encode : Dynamic.Op U → Fin r → ℕ)
    (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
          (Dictionary.empty U) ops ν₀ ν_final T_ops)
    {LB : ℝ}
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result S_max w},
      (∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      LB ≤ ∑' ops, (insertQueryDeleteDist U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (LB / (2 * (persCount input : ℝ) + 1)) ≤
      ∑' ops, insertQueryDeleteDist U V n hU hV ops *
        flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  simpa only [modeDist_true] using
    le_expectedFlatTime_mode_of_det_indexedScheme true hn hU hV hspace p_op encode decode ν₀
      hsupp₀ ((modeHorizon_true n).symm ▸ hex_corr) fun hcorr => by
        simpa only [modeDist_true] using hlb (modeHorizon_true n ▸ hcorr)

/-- Transfer any deterministic step-indexed `IndexedScheme` lower bound over `insertDeleteDist`
directly to the exact intrinsic expected non-`halt` body-instruction count
`flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops`. -/
theorem expectedFlatTime_update_ge_of_indexedScheme
    {B : Basis} {U V n r w base space S_max : ℕ} {input : Fin r → Bool} {Latent : Type z}
    (hn : 1 ≤ n) (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (hspace : space + persCount input ≤ S_max)
    (p_op : Program B r)
    (encode : Dynamic.Op U → Fin r → ℕ)
    (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
          (Dictionary.empty U) ops ν₀ ν_final T_ops)
    {LB : ℝ}
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result S_max w},
      (∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      LB ≤ ∑' ops, (insertDeleteDist U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (LB / (2 * (persCount input : ℝ) + 1)) ≤
      ∑' ops, insertDeleteDist U V n hU hV ops *
        flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  simpa only [modeDist_false] using
    le_expectedFlatTime_mode_of_det_indexedScheme false hn hU hV hspace p_op encode decode ν₀
      hsupp₀ ((modeHorizon_false n).symm ▸ hex_corr) fun hcorr => by
        simpa only [modeDist_false] using hlb (modeHorizon_false n ▸ hcorr)

/-- Transfer any deterministic step-indexed `IndexedScheme` lower bound over
`insertQueryDeleteDist` to the certified expected-amortized instruction budget of a zero-error
`WordRAM.Randomized.StateTransitionImpl` on `Dynamic.spec U V n` (including deterministic
`WordRAM.StateTransitionImpl`s via `StateTransitionImpl.toRandomized`). -/
theorem expectedTotalCost_ge_of_indexedScheme
    {B : Basis} {U V n r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base params
      (Dictionary.empty U))
    (hbase : Fits w base)
    (hparams_fit : ∀ j, Fits w (params j))
    (hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
    (hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    {LB : ℝ}
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result S_max w},
      (∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      LB ≤ ∑' ops, (insertQueryDeleteDist U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (LB / (2 * (persistentRegCount P : ℝ) + 1)) ≤
      (C.initPotential : ℝ≥0∞) +
        ∑' ops, insertQueryDeleteDist U V n hU hV ops *
          ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  simpa only [modeDist_true] using
    le_expectedTotalCost_mode_of_det_indexedScheme true hU hV C hbase hparams_fit hparams_fr
      hparams_agree hspace fun hcorr => by
        simpa only [modeDist_true] using hlb (by rwa [modeHorizon_true] at hcorr)

/-- Transfer any deterministic step-indexed `IndexedScheme` lower bound over `insertDeleteDist` to
the certified expected-amortized instruction budget of a zero-error
`WordRAM.Randomized.StateTransitionImpl` on `Dynamic.spec U V n` (including deterministic
`WordRAM.StateTransitionImpl`s via `StateTransitionImpl.toRandomized`). -/
theorem expectedTotalCost_update_ge_of_indexedScheme
    {B : Basis} {U V n r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base params
      (Dictionary.empty U))
    (hbase : Fits w base)
    (hparams_fit : ∀ j, Fits w (params j))
    (hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
    (hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    {LB : ℝ}
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result S_max w},
      (∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      LB ≤ ∑' ops, (insertDeleteDist U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (LB / (2 * (persistentRegCount P : ℝ) + 1)) ≤
      (C.initPotential : ℝ≥0∞) +
        ∑' ops, insertDeleteDist U V n hU hV ops *
          ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  simpa only [modeDist_false] using
    le_expectedTotalCost_mode_of_det_indexedScheme false hU hV C hbase hparams_fit hparams_fr
      hparams_agree hspace fun hcorr => by
        simpa only [modeDist_false] using hlb (by rwa [modeHorizon_false] at hcorr)

/-! ### 3. Primary Word-RAM Headline Lower Bounds: Actual Expected Running Time -/

private theorem scale_div_pers_le {c_cp X : ℝ} {p r_max : ℕ}
    (hc : 0 < c_cp) (hX : 0 ≤ X) (hp : p ≤ r_max) :
    (c_cp / (2 * (r_max : ℝ) + 1)) * X ≤ (c_cp * X) / (2 * (p : ℝ) + 1) := by
  have hle : 2 * (p : ℝ) + 1 ≤ 2 * (r_max : ℝ) + 1 := by
    linarith [(Nat.cast_le.mpr hp : (p : ℝ) ≤ r_max)]
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (mul_nonneg hc.le hX) (by positivity) hle

private theorem logb_div_max_nonneg {n : ℕ} {R : ℝ} (hn : 2 ≤ n) (hR : R ≤ (n : ℝ)) :
    0 ≤ Real.logb 2 ((n : ℝ) / max R 1) := by
  have hdiv : 1 ≤ (n : ℝ) / max R 1 :=
    (one_le_div (lt_of_lt_of_le zero_lt_one (_root_.le_max_right R 1))).mpr
      (max_le hR (by exact_mod_cast (show 1 ≤ n by omega)))
  exact Real.logb_nonneg (by norm_num) hdiv

private theorem expectedFlatTime_scaled_of_mode (withQueries : Bool)
    {B : Basis} {U V n r w base space r_max : ℕ} {input : Fin r → Bool} {Latent : Type z}
    {c_cp X : ℝ} (hc_cp : 0 < c_cp) (hX : 0 ≤ X)
    (hn : 2 ≤ n) (hU : 2 * n ≤ U) (hV : 1 ≤ V) (hpers : persCount input ≤ r_max)
    (p_op : Program B r)
    (encode : Dynamic.Op U → Fin r → ℕ)
    (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
          (Dictionary.empty U) ops ν₀ ν_final T_ops)
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result (space + persCount input) w},
      (∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      c_cp * X ≤
        ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (c_cp / (2 * (r_max : ℝ) + 1) * X) ≤
      ∑' ops, modeDist withQueries U V n hU hV ops *
        flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops :=
  (ENNReal.ofReal_le_ofReal (scale_div_pers_le hc_cp hX hpers)).trans
    (le_expectedFlatTime_mode_of_det_indexedScheme withQueries (Nat.le_of_succ_le hn) hU hV le_rfl
      p_op encode decode ν₀ hsupp₀ hex_corr hlb)

private theorem expectedFlatTime_scaled_iqd
    {B : Basis} {U V n r w base space r_max : ℕ} {input : Fin r → Bool} {Latent : Type z}
    {c_cp Y : ℝ} (hc_cp : 0 < c_cp) (hY : 0 ≤ Y)
    (hn : 2 ≤ n) (hU2 : 2 * n ≤ U) (hV : 1 ≤ V) (hpers : persCount input ≤ r_max)
    (p_op : Program B r)
    (encode : Dynamic.Op U → Fin r → ℕ)
    (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
          (Dictionary.empty U) ops ν₀ ν_final T_ops)
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result (space + persCount input) w},
      (∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      c_cp * (n : ℝ) * Y ≤
        ∑' ops, (insertQueryDeleteDist U V n hU2 hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (c_cp / (2 * (r_max : ℝ) + 1) * (n : ℝ) * Y) ≤
      ∑' ops, insertQueryDeleteDist U V n hU2 hV ops *
        flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  simpa only [modeDist_true, mul_assoc] using
    expectedFlatTime_scaled_of_mode true hc_cp (mul_nonneg (Nat.cast_nonneg n) hY) hn hU2 hV hpers
      p_op encode decode ν₀ hsupp₀ ((modeHorizon_true n).symm ▸ hex_corr) fun hcorr => by
        simpa only [modeDist_true, mul_assoc] using hlb (modeHorizon_true n ▸ hcorr)

private theorem expectedFlatTime_scaled_upd
    {B : Basis} {U V n r w base space r_max : ℕ} {input : Fin r → Bool} {Latent : Type z}
    {c_cp Y : ℝ} (hc_cp : 0 < c_cp) (hY : 0 ≤ Y)
    (hn : 2 ≤ n) (hU2 : 2 * n ≤ U) (hV : 1 ≤ V) (hpers : persCount input ≤ r_max)
    (p_op : Program B r)
    (encode : Dynamic.Op U → Fin r → ℕ)
    (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
        ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
          (Dictionary.empty U) ops ν₀ ν_final T_ops)
    (hlb : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result (space + persCount input) w},
      (∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      c_cp * (n : ℝ) * Y ≤
        ∑' ops, (insertDeleteDist U V n hU2 hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal (c_cp / (2 * (r_max : ℝ) + 1) * (n : ℝ) * Y) ≤
      ∑' ops, insertDeleteDist U V n hU2 hV ops *
        flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  simpa only [modeDist_false, mul_assoc] using
    expectedFlatTime_scaled_of_mode false hc_cp (mul_nonneg (Nat.cast_nonneg n) hY) hn hU2 hV hpers
      p_op encode decode ν₀ hsupp₀ ((modeHorizon_false n).symm ▸ hex_corr) fun hcorr => by
        simpa only [modeDist_false, mul_assoc] using hlb (modeHorizon_false n ▸ hcorr)

/-- Word-RAM **Theorem 1.1 / Theorem 3.1** ([LiLiangYuZhou2023], Section 1, p. 1 and footnote 1 /
PDF p. 2, and Section 3, pp. 10–13 / PDF pp. 11–14; [Yao1977]): for any `α > 0`, `c_R ≥ 0`,
`c_w ≥ 0`, and persistent-register bound `r_max`, there exists `c > 0` such that any zero-error
(Las Vegas) or deterministic flat Word-RAM program `p_op : Program B r` realizing
`Dynamic.spec U V n` from `ν₀` up to horizon `4 * n + 1` with `persCount input ≤ r_max` and
persistent bit budget `(((space + persCount input) * w : ℕ) : ℝ) ≤ benchmarkBits U V n +
c_R * n * max (log^{(k)} n) 1` (`1 ≤ k ≤ log* n`) has exact intrinsic expected non-`halt`
body-instruction count `flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops` at least
`ENNReal.ofReal (c * n * k)` over oblivious `insertQueryDeleteDist` (hence also `flatExpectedTime`
and any admissible `ExecFlatProgramOps` budget `T_ops` via `flatExpectedBodyTime_le`).
Specializing `k = Nat.logStar n` (`max (Nat.iterLog (Nat.logStar n) n) 1 = 1` for `2 ≤ n`) yields
`Ω(n * log* n)` under `O(n)` bits of redundancy; Monte Carlo error and adaptive sequence
adversaries are out of scope. -/
theorem expectedFlatTime_ge_of_iterLog_redundancy {α c_R c_w : ℝ} (r_max : ℕ)
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n k r w base space : ℕ} {input : Fin r → Bool} {Latent : Type z}
        (_hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hpers : persCount input ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : (((space + persCount input) * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (p_op : Program B r)
        (encode : Dynamic.Op U → Fin r → ℕ)
        (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
        (ν₀ : PMF (Latent × Data r))
        (_hsupp₀ : ∀ p ∈ ν₀.support,
          p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
        (_hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
            ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
              (Dictionary.empty U) ops ν₀ ν_final T_ops),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  obtain ⟨c_cp, hc_cp, hdet⟩ := det_expectedSeqProbes_ge_of_iterLog_redundancy hα hcR hcw
  refine ⟨c_cp / (2 * (r_max : ℝ) + 1), by positivity, fun hn hU hU_poly hV hk_lo hk_hi hpers hw
    hspace p_op encode decode ν₀ hsupp₀ hex_corr =>
    expectedFlatTime_scaled_iqd hc_cp (Nat.cast_nonneg _) hn _ hV hpers p_op encode decode ν₀
      hsupp₀ hex_corr fun hcorr =>
        hdet hn hU hU_poly hV hk_lo hk_hi hw hspace hcorr⟩

/-- Word-RAM **Theorem 1.2 / Theorem 6.1** ([LiLiangYuZhou2023], Section 1, p. 1 footnote 1 and
p. 2 / PDF pp. 2–3, and Section 6, pp. 25–26 / PDF pp. 26–27; [Yao1977]): for any `α > 0`,
`c_w ≥ 0`, and persistent-register bound `r_max`, there exists `c > 0` such that any zero-error
(Las Vegas) or deterministic flat Word-RAM program `p_op : Program B r` realizing
`Dynamic.spec U V n` up to horizon `4 * n + 1` with `persCount input ≤ r_max` and `R ≤ n` bits of
redundancy (`(((space + persCount input) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R`) has exact
intrinsic expected non-`halt` body-instruction count `flatExpectedBodyTime` at least
`ENNReal.ofReal (c * n * log₂(n / max R 1))` on oblivious `insertQueryDeleteDist` (vanishing at
`R = n`; see `expectedFlatTime_ge_iterLogStar_add_log_div` for the combined bound across
`R ≤ c_R * n`). -/
theorem expectedFlatTime_ge_of_sublinear_redundancy {α c_w : ℝ} (r_max : ℕ)
    (hα : 0 < α) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n r w base space : ℕ} {R : ℝ} {input : Fin r → Bool} {Latent : Type z}
        (_hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ (n : ℝ))
        (_hpers : persCount input ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : (((space + persCount input) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (p_op : Program B r)
        (encode : Dynamic.Op U → Fin r → ℕ)
        (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
        (ν₀ : PMF (Latent × Data r))
        (_hsupp₀ : ∀ p ∈ ν₀.support,
          p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
        (_hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
            ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
              (Dictionary.empty U) ops ν₀ ν_final T_ops),
        ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  obtain ⟨c_cp, hc_cp, hdet⟩ := det_expectedSeqProbes_ge_of_sublinear_redundancy hα hcw
  refine ⟨c_cp / (2 * (r_max : ℝ) + 1), by positivity, fun hn hU hU_poly hV hR_hi hpers hw
    hspace p_op encode decode ν₀ hsupp₀ hex_corr =>
    expectedFlatTime_scaled_iqd hc_cp (logb_div_max_nonneg hn hR_hi) hn _ hV hpers p_op encode
      decode ν₀ hsupp₀ hex_corr fun hcorr =>
        hdet hn hU hU_poly hV hR_hi hw hspace hcorr⟩

/-- Combined Word-RAM **Theorems 1.1 & 1.2**
(`Ω(n * (log* n + max 0 (log₂(n / max R 1))))` exact intrinsic expected non-`halt` body
instructions `flatExpectedBodyTime`) across all `R ≤ c_R * n` in the zero-error (Las Vegas) or
deterministic oblivious model ([LiLiangYuZhou2023], Section 1, pp. 1–2 and footnote 1 / PDF
pp. 2–3, and Section 7, pp. 26–27 / PDF pp. 27–28; [Yao1977]). -/
theorem expectedFlatTime_ge_iterLogStar_add_log_div {α c_R c_w : ℝ} (r_max : ℕ)
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n r w base space : ℕ} {R : ℝ} {input : Fin r → Bool} {Latent : Type z}
        (_hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hpers : persCount input ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : (((space + persCount input) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (p_op : Program B r)
        (encode : Dynamic.Op U → Fin r → ℕ)
        (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
        (ν₀ : PMF (Latent × Data r))
        (_hsupp₀ : ∀ p ∈ ν₀.support,
          p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
        (_hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
            ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
              (Dictionary.empty U) ops ν₀ ν_final T_ops),
        ENNReal.ofReal (c * (n : ℝ) *
          ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  obtain ⟨c_cp, hc_cp, hdet⟩ := det_expectedSeqProbes_ge_iterLogStar_add_log_div hα hcR hcw
  refine ⟨c_cp / (2 * (r_max : ℝ) + 1), by positivity, fun hn hU hU_poly hV hR_hi hpers hw
    hspace p_op encode decode ν₀ hsupp₀ hex_corr =>
    expectedFlatTime_scaled_iqd hc_cp (add_nonneg (Nat.cast_nonneg _) (_root_.le_max_left 0 _)) hn
      _ hV hpers p_op encode decode ν₀ hsupp₀ hex_corr fun hcorr =>
        hdet hn hU hU_poly hV hR_hi hw hspace hcorr⟩

/-- Word-RAM **Theorem 1.3(1)** ([LiLiangYuZhou2023], Section 1, p. 1 footnote 1 and p. 2 /
PDF pp. 2–3, and Section 8, pp. 27–30 / PDF pp. 28–31; [Yao1977]): update-only (`insertDeleteDist`)
`Ω(n * k)` exact intrinsic expected non-`halt` body-instruction (`flatExpectedBodyTime`) lower
bound for zero-error (Las Vegas) or deterministic flat Word-RAM programs when `3 * n ≤ U` and
`U ^ (2 + α_V) ≤ V * n ^ 2` under redundancy `≤ c_R * n * max (log^{(k)} n) 1` (with horizon
`3 * n + 1` for `decodeDict`, no query-time constraint, and `k = Nat.logStar n` yielding
`Ω(n * log* n)` under `O(n)` redundancy). -/
theorem expectedFlatTime_update_ge_iterLog {α_V c_R c_w : ℝ} (r_max : ℕ)
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n k r w base space : ℕ} {input : Fin r → Bool} {Latent : Type z}
        (_hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hpers : persCount input ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : (((space + persCount input) * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (p_op : Program B r)
        (encode : Dynamic.Op U → Fin r → ℕ)
        (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
        (ν₀ : PMF (Latent × Data r))
        (_hsupp₀ : ∀ p ∈ ν₀.support,
          p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
        (_hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
            ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
              (Dictionary.empty U) ops ν₀ ν_final T_ops),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  obtain ⟨c_cp, hc_cp, hdet⟩ := det_expectedSeqProbes_update_ge_iterLog hα_V hcR hcw
  refine ⟨c_cp / (2 * (r_max : ℝ) + 1), by positivity, fun hn hU hV hV_lo hk_lo hk_hi hpers hw
    hspace p_op encode decode ν₀ hsupp₀ hex_corr =>
    expectedFlatTime_scaled_upd hc_cp (Nat.cast_nonneg _) hn _ hV hpers p_op encode decode ν₀
      hsupp₀ hex_corr fun hcorr =>
        hdet hn hU hV hV_lo hk_lo hk_hi hw hspace hcorr⟩

/-- Word-RAM **Theorem 1.3(2)** ([LiLiangYuZhou2023], Section 1, p. 1 footnote 1 and p. 2 /
PDF pp. 2–3, and Section 8, pp. 27–30 / PDF pp. 28–31; [Yao1977]): update-only (`insertDeleteDist`)
`Ω(n * log₂(n / max R 1))` exact intrinsic expected non-`halt` body-instruction
(`flatExpectedBodyTime`) lower bound for zero-error (Las Vegas) or deterministic flat Word-RAM
programs when `3 * n ≤ U`, `U ^ (2 + α_V) ≤ V * n ^ 2`, and `R ≤ n` (vanishing at `R = n`). -/
theorem expectedFlatTime_update_ge_sublinear {α_V c_w : ℝ} (r_max : ℕ)
    (hα_V : 0 < α_V) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n r w base space : ℕ} {R : ℝ} {input : Fin r → Bool} {Latent : Type z}
        (_hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ (n : ℝ))
        (_hpers : persCount input ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : (((space + persCount input) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (p_op : Program B r)
        (encode : Dynamic.Op U → Fin r → ℕ)
        (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
        (ν₀ : PMF (Latent × Data r))
        (_hsupp₀ : ∀ p ∈ ν₀.support,
          p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
        (_hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
            ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
              (Dictionary.empty U) ops ν₀ ν_final T_ops),
        ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  obtain ⟨c_cp, hc_cp, hdet⟩ := det_expectedSeqProbes_update_ge_sublinear hα_V hcw
  refine ⟨c_cp / (2 * (r_max : ℝ) + 1), by positivity, fun hn hU hV hV_lo hR_hi hpers hw
    hspace p_op encode decode ν₀ hsupp₀ hex_corr =>
    expectedFlatTime_scaled_upd hc_cp (logb_div_max_nonneg hn hR_hi) hn _ hV hpers p_op encode
      decode ν₀ hsupp₀ hex_corr fun hcorr =>
        hdet hn hU hV hV_lo hR_hi hw hspace hcorr⟩

/-- Combined Word-RAM **Theorem 1.3(1)–(2)**
(`Ω(n * (log* n + max 0 (log₂(n / max R 1))))` exact intrinsic expected non-`halt` body
instructions `flatExpectedBodyTime`) on `insertDeleteDist` across all `R ≤ c_R * n` in the
zero-error (Las Vegas) or deterministic oblivious model ([LiLiangYuZhou2023], Section 1, pp. 1–2
and footnote 1 / PDF pp. 2–3, and Section 8, pp. 27–30 / PDF pp. 28–31; [Yao1977]). -/
theorem expectedFlatTime_update_ge_iterLogStar_add_log_div {α_V c_R c_w : ℝ} (r_max : ℕ)
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n r w base space : ℕ} {R : ℝ} {input : Fin r → Bool} {Latent : Type z}
        (_hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hpers : persCount input ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : (((space + persCount input) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (p_op : Program B r)
        (encode : Dynamic.Op U → Fin r → ℕ)
        (decode : (o : Dynamic.Op U) → ℕ → (Fin r → ℕ) → Option o.Result)
        (ν₀ : PMF (Latent × Data r))
        (_hsupp₀ : ∀ p ∈ ν₀.support,
          p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
        (_hex_corr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
            ExecFlatProgramOps (Dynamic.spec U V n) Latent w base space p_op input encode decode
              (Dictionary.empty U) ops ν₀ ν_final T_ops),
        ENNReal.ofReal (c * (n : ℝ) *
          ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            flatExpectedBodyTime w p_op input encode (ν₀.map Prod.snd) ops := by
  obtain ⟨c_cp, hc_cp, hdet⟩ := det_expectedSeqProbes_update_ge_iterLogStar_add_log_div hα_V hcR hcw
  refine ⟨c_cp / (2 * (r_max : ℝ) + 1), by positivity, fun hn hU hV hV_lo hR_hi hpers hw
    hspace p_op encode decode ν₀ hsupp₀ hex_corr =>
    expectedFlatTime_scaled_upd hc_cp (add_nonneg (Nat.cast_nonneg _) (_root_.le_max_left 0 _)) hn
      _ hV hpers p_op encode decode ν₀ hsupp₀ hex_corr fun hcorr =>
        hdet hn hU hV hV_lo hR_hi hw hspace hcorr⟩

/-! ### 4. Certified-Budget Corollaries for `WordRAM.Randomized.StateTransitionImpl` -/

/-- Certified-budget corollary of `expectedFlatTime_ge_of_iterLog_redundancy` ([CLRS2009], Section
17.3): lower-bounds the potential-amortized instruction budget `C.initPotential + E[totalCost
C.charge]` of any zero-error `WordRAM.Randomized.StateTransitionImpl` (including deterministic
`WordRAM.StateTransitionImpl`s via `StateTransitionImpl.toRandomized`) on `insertQueryDeleteDist`.
-/
theorem expectedTotalCost_ge_of_iterLog_redundancy {α c_R c_w : ℝ} (r_max : ℕ)
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n k r_ds k_init w base : ℕ}
        {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
        (_hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hpers : persistentRegCount P ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base
          params (Dictionary.empty U))
        (_hspace : (((C.space + persistentRegCount P) * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (_hbase : Fits w base)
        (_hparams_fit : ∀ j, Fits w (params j))
        (_hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
        (_hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          (C.initPotential : ℝ≥0∞) +
            ∑' ops, insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨c, hc, hflat⟩ := expectedFlatTime_ge_of_iterLog_redundancy.{0} r_max hα hcR hcw
  refine ⟨c, hc, fun hn hU hU_poly hV hk_lo hk_hi hpers hw C hspace hbase hpf hpfr hpag => ?_⟩
  rw [persistentRegCount_eq_persCount] at hpers hspace
  exact totalCost_ge_of_flat_fn _ (fun _ hops =>
      (validHistory_of_mem_support_insertQueryDeleteDist hops).1) C hbase hpf hpfr hpag
    (hflat hn hU hU_poly hV hk_lo hk_hi hpers hw hspace _ C.encode fun o _ regs => C.decode o regs)

/-- Certified-budget corollary of `expectedFlatTime_ge_of_sublinear_redundancy` ([CLRS2009],
Section 17.3): lower-bounds `C.initPotential + E[totalCost C.charge]` for any zero-error
`WordRAM.Randomized.StateTransitionImpl` (or `StateTransitionImpl.toRandomized`) under `R ≤ n` bits
of redundancy on `insertQueryDeleteDist` (vanishing at `R = n`). -/
theorem expectedTotalCost_ge_of_sublinear_redundancy {α c_w : ℝ} (r_max : ℕ)
    (hα : 0 < α) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n r_ds k_init w base : ℕ} {R : ℝ}
        {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
        (_hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ (n : ℝ))
        (_hpers : persistentRegCount P ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base
          params (Dictionary.empty U))
        (_hspace : (((C.space + persistentRegCount P) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (_hbase : Fits w base)
        (_hparams_fit : ∀ j, Fits w (params j))
        (_hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
        (_hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j),
        ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
          (C.initPotential : ℝ≥0∞) +
            ∑' ops, insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨c, hc, hflat⟩ := expectedFlatTime_ge_of_sublinear_redundancy.{0} r_max hα hcw
  refine ⟨c, hc, fun hn hU hU_poly hV hR_hi hpers hw C hspace hbase hpf hpfr hpag => ?_⟩
  rw [persistentRegCount_eq_persCount] at hpers hspace
  exact totalCost_ge_of_flat_fn _ (fun _ hops =>
      (validHistory_of_mem_support_insertQueryDeleteDist hops).1) C hbase hpf hpfr hpag
    (hflat hn hU hU_poly hV hR_hi hpers hw hspace _ C.encode fun o _ regs => C.decode o regs)

/-- Certified-budget corollary of `expectedFlatTime_ge_iterLogStar_add_log_div` ([CLRS2009],
Section 17.3): lower-bounds `C.initPotential + E[totalCost C.charge]` across all `R ≤ c_R * n` on
`insertQueryDeleteDist` for any zero-error `WordRAM.Randomized.StateTransitionImpl` (or
`StateTransitionImpl.toRandomized`). -/
theorem expectedTotalCost_ge_iterLogStar_add_log_div {α c_R c_w : ℝ} (r_max : ℕ)
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n r_ds k_init w base : ℕ} {R : ℝ}
        {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
        (_hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hpers : persistentRegCount P ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base
          params (Dictionary.empty U))
        (_hspace : (((C.space + persistentRegCount P) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (_hbase : Fits w base)
        (_hparams_fit : ∀ j, Fits w (params j))
        (_hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
        (_hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j),
        ENNReal.ofReal (c * (n : ℝ) *
          ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
          (C.initPotential : ℝ≥0∞) +
            ∑' ops, insertQueryDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨c, hc, hflat⟩ := expectedFlatTime_ge_iterLogStar_add_log_div.{0} r_max hα hcR hcw
  refine ⟨c, hc, fun hn hU hU_poly hV hR_hi hpers hw C hspace hbase hpf hpfr hpag => ?_⟩
  rw [persistentRegCount_eq_persCount] at hpers hspace
  exact totalCost_ge_of_flat_fn _ (fun _ hops =>
      (validHistory_of_mem_support_insertQueryDeleteDist hops).1) C hbase hpf hpfr hpag
    (hflat hn hU hU_poly hV hR_hi hpers hw hspace _ C.encode fun o _ regs => C.decode o regs)

/-- Certified-budget corollary of `expectedFlatTime_update_ge_iterLog` ([CLRS2009], Section 17.3):
lower-bounds `C.initPotential + E[totalCost C.charge]` on update-only `insertDeleteDist` for any
zero-error `WordRAM.Randomized.StateTransitionImpl` (or `StateTransitionImpl.toRandomized`). -/
theorem expectedTotalCost_update_ge_iterLog {α_V c_R c_w : ℝ} (r_max : ℕ)
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n k r_ds k_init w base : ℕ}
        {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
        (_hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hpers : persistentRegCount P ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base
          params (Dictionary.empty U))
        (_hspace : (((C.space + persistentRegCount P) * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (_hbase : Fits w base)
        (_hparams_fit : ∀ j, Fits w (params j))
        (_hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
        (_hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          (C.initPotential : ℝ≥0∞) +
            ∑' ops, insertDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨c, hc, hflat⟩ := expectedFlatTime_update_ge_iterLog.{0} r_max hα_V hcR hcw
  refine ⟨c, hc, fun hn hU hV hV_lo hk_lo hk_hi hpers hw C hspace hbase hpf hpfr hpag => ?_⟩
  rw [persistentRegCount_eq_persCount] at hpers hspace
  exact totalCost_ge_of_flat_fn _ (fun _ hops =>
      (validHistory_of_mem_support_insertDeleteDist hops).1) C hbase hpf hpfr hpag
    (hflat hn hU hV hV_lo hk_lo hk_hi hpers hw hspace _ C.encode fun o _ regs => C.decode o regs)

/-- Certified-budget corollary of `expectedFlatTime_update_ge_sublinear` ([CLRS2009], Section
17.3): lower-bounds `C.initPotential + E[totalCost C.charge]` on update-only `insertDeleteDist`
under `R ≤ n` bits of redundancy (vanishing at `R = n`) for any zero-error
`WordRAM.Randomized.StateTransitionImpl` (or `StateTransitionImpl.toRandomized`). -/
theorem expectedTotalCost_update_ge_sublinear {α_V c_w : ℝ} (r_max : ℕ)
    (hα_V : 0 < α_V) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n r_ds k_init w base : ℕ} {R : ℝ}
        {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
        (_hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ (n : ℝ))
        (_hpers : persistentRegCount P ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base
          params (Dictionary.empty U))
        (_hspace : (((C.space + persistentRegCount P) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (_hbase : Fits w base)
        (_hparams_fit : ∀ j, Fits w (params j))
        (_hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
        (_hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j),
        ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
          (C.initPotential : ℝ≥0∞) +
            ∑' ops, insertDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨c, hc, hflat⟩ := expectedFlatTime_update_ge_sublinear.{0} r_max hα_V hcw
  refine ⟨c, hc, fun hn hU hV hV_lo hR_hi hpers hw C hspace hbase hpf hpfr hpag => ?_⟩
  rw [persistentRegCount_eq_persCount] at hpers hspace
  exact totalCost_ge_of_flat_fn _ (fun _ hops =>
      (validHistory_of_mem_support_insertDeleteDist hops).1) C hbase hpf hpfr hpag
    (hflat hn hU hV hV_lo hR_hi hpers hw hspace _ C.encode fun o _ regs => C.decode o regs)

/-- Certified-budget corollary of `expectedFlatTime_update_ge_iterLogStar_add_log_div` ([CLRS2009],
Section 17.3): lower-bounds `C.initPotential + E[totalCost C.charge]` on update-only
`insertDeleteDist` across all `R ≤ c_R * n` for any zero-error
`WordRAM.Randomized.StateTransitionImpl` (or `StateTransitionImpl.toRandomized`). -/
theorem expectedTotalCost_update_ge_iterLogStar_add_log_div {α_V c_R c_w : ℝ} (r_max : ℕ)
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {B : Basis} {U V n r_ds k_init w base : ℕ} {R : ℝ}
        {P : SubroutineCode B r_ds k_init} {params : Fin k_init → ℕ}
        (_hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hpers : persistentRegCount P ≤ r_max)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (C : DataStructure.WordRAM.Randomized.StateTransitionImpl P (Dynamic.spec U V n) w base
          params (Dictionary.empty U))
        (_hspace : (((C.space + persistentRegCount P) * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (_hbase : Fits w base)
        (_hparams_fit : ∀ j, Fits w (params j))
        (_hparams_fr : ∀ j, P.initParams j = P.frontierReg → params j = base)
        (_hparams_agree : ∀ i j, P.initParams i = P.initParams j → params i = params j),
        ENNReal.ofReal (c * (n : ℝ) *
          ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
          (C.initPotential : ℝ≥0∞) +
            ∑' ops, insertDeleteDist U V n
              (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
              ((Dynamic.spec U V n).totalCost C.charge (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨c, hc, hflat⟩ := expectedFlatTime_update_ge_iterLogStar_add_log_div.{0} r_max hα_V hcR hcw
  refine ⟨c, hc, fun hn hU hV hV_lo hR_hi hpers hw C hspace hbase hpf hpfr hpag => ?_⟩
  rw [persistentRegCount_eq_persCount] at hpers hspace
  exact totalCost_ge_of_flat_fn _ (fun _ hops =>
      (validHistory_of_mem_support_insertDeleteDist hops).1) C hbase hpf hpfr hpag
    (hflat hn hU hV hV_lo hR_hi hpers hw hspace _ C.encode fun o _ regs => C.decode o regs)

end Cslib.DataStructure.Dictionary.WordRAM
