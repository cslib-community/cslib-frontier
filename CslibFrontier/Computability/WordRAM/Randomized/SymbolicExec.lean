/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Computability.WordRAM.Randomized.Expected
public import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Tactic.SuppCases

/-!
# Symbolic execution of structured randomized word-RAM code

Weakest-precondition wrappers and symbolic-execution tactics extending `Cslib.WordRAM.WP`
(`wram_exec`) to structured randomized execution:

* `Cslib.WordRAM.WP.Rand w c x Q`: weakest-precondition form of `ExecRand w c x m`
  (`∃ m, ExecRand w c x m ∧ Q m`).
* `Cslib.WordRAM.WP.RandWithin w c x P Q`: weakest-precondition form of `ExecRandWithin w c x P T R`
  with residual step and `rand`-query budgets (`∃ t q, ExecRandWithin w c x P t q ∧ Q t q`).
* `Cslib.WordRAM.WP.Dist w c x Q`: weakest-precondition form of `ExecCodeDist w c x μ T`
  (`∃ μ T, ExecCodeDist w c x μ T ∧ Q μ T`).

The tactic `wram_rand_exec` steps straight-line deterministic instructions (`Code.op`),
conditionals (`Code.branch`, or stops with `-split`), and uniform draws (`Code.rand`, both at a
leaf and at the head of `Code.seq`), reassociating left-nested `Code.seq` automatically and
reusing the register/memory simprocs and `fits` discharger of `wram_exec`.

The tactic `wram_rand_call` consumes a proved deterministic (`Exec`, `ExecWithin`) or randomized
(`ExecRand`, `ExecRandWithin`, `ExecCodeDist`) contract at the head of a `WP.Rand`,
`WP.RandWithin`, or `WP.Dist` goal (including across `Code.rename f` via `renamed hf`), exposing a
`WP` continuation whose residual `ProbComp` or `PMF` family unifies by higher-order pattern
matching without manual `m₂` or `μ₂` annotations.

## Main definitions

* `Cslib.WordRAM.WP.Rand`: weakest-precondition wrapper for `ExecRand`.
* `Cslib.WordRAM.WP.RandWithin`: weakest-precondition wrapper for `ExecRandWithin`.
* `Cslib.WordRAM.WP.Dist`: weakest-precondition wrapper for `ExecCodeDist`.
* `wram_rand_exec`: straight-line and `rand` symbolic execution for randomized structured code.
* `wram_rand_call`: consume a deterministic or randomized routine specification at a `WP.Rand`,
  `WP.RandWithin`, or `WP.Dist` stop.

## Main results

* `Cslib.WordRAM.ExecRand.seq_det`: compose an `ExecRand` prefix with a family of deterministic
  `Exec` continuations.
* `Cslib.WordRAM.ExecCodeDist.of_execRand_le`: lift a pathwise step-bounded `ExecRand` into
  `ExecCodeDist`.
* `Cslib.WordRAM.WP.Rand.execRand`, `Cslib.WordRAM.WP.RandWithin.execRandWithin`,
  `Cslib.WordRAM.WP.Dist.execCodeDist`: extract structured randomized execution certificates from
  their weakest preconditions, together with the `seq_*`, `rand`, and `branch_*` rules applied by
  `wram_rand_exec` and `wram_rand_call`.
-/

public section

open scoped ENNReal

namespace Cslib.WordRAM

variable {B : Basis} {r r' : ℕ}

/-! ## Shared structural lemmas for `ExecRand`, `ExecRandWithin`, and `ExecCodeDist` -/

section Structural

variable {w : ℕ}

/-- Post-compose a deterministic continuation `Exec w c₂ y (f y) (n₂ y)` onto an exact randomized
execution `ExecRand w c₁ x m₁`. -/
theorem ExecRand.seq_det {c₁ c₂ : Code B r} {x : Data r}
    {m₁ : ProbComp (Data r × ℕ)} {f : Data r → Data r} {n₂ : Data r → ℕ}
    (h₁ : ExecRand w c₁ x m₁)
    (h₂ : ∀ y n, (y, n) ∈ m₁.support → Exec w c₂ y (f y) (n₂ y)) :
    ExecRand w (.seq c₁ c₂) x ((fun z => (f z.1, z.2 + n₂ z.1)) <$> m₁) := by
  have hseq := ExecRand.seq h₁ (m₂ := fun y => pure (f y, n₂ y))
    fun z hz => (h₂ z.1 z.2 hz).execRand
  simpa only [pure_bind, ← bind_pure_comp] using hseq

private theorem execRand_congr_eq {c : Code B r} {x : Data r} {m m' : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) (heq : m = m') : ExecRand w c x m' :=
  heq ▸ h

private theorem execRand_rand_seq {dst src : Fin r} {x : Data r} {a : ℕ} {c₂ : Code B r}
    (hs : x.regs src = a) (hfit : Fits w a)
    {m₂ : Fin (a + 1) → ProbComp (Data r × ℕ)}
    (h₂ : ∀ k : Fin (a + 1), ExecRand w c₂ (x.set dst k.val) (m₂ k)) :
    ExecRand w (.seq (.rand dst src) c₂) x (do
      let k ← ProbComp.unifFin a
      let z₂ ← m₂ k
      pure (z₂.1, 1 + z₂.2)) := by
  classical
  have hr : ExecRand (B := B) w (.rand dst src) x (do
      let k ← ProbComp.unifFin a
      pure (x.set dst k.val, 1)) := by
    have h0 := ExecRand.rand (B := B) (dst := dst) (src := src) (hs ▸ hfit)
    rwa [hs] at h0
  let m₂' : Data r → ProbComp (Data r × ℕ) := fun d =>
    if h : d.regs dst < a + 1 then m₂ ⟨d.regs dst, h⟩ else pure (d, 0)
  have hseq := ExecRand.seq hr (m₂ := m₂') fun z hz => by
    supp_cases hz with ⟨k, rfl⟩
    simp only [m₂', Data.set_regs, Function.update_self, k.isLt, ↓reduceDIte]
    exact h₂ k
  refine execRand_congr_eq hseq ?_
  simp only [bind_assoc, pure_bind]
  refine congrArg (ProbComp.unifFin a >>= ·) (funext fun k => ?_)
  simp only [m₂', Data.set_regs, Function.update_self, k.isLt, ↓reduceDIte]

private theorem execRand_seq_inv {w : ℕ} {c₁ c₂ : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w (.seq c₁ c₂) x m) :
    ∃ (m₁ : ProbComp (Data r × ℕ)) (m₂ : Data r → ProbComp (Data r × ℕ)),
      ExecRand w c₁ x m₁ ∧
      (∀ z ∈ m₁.support, ExecRand w c₂ z.1 (m₂ z.1)) ∧
      m = (do let z₁ ← m₁; let z₂ ← m₂ z₁.1; pure (z₂.1, z₁.2 + z₂.2)) := by
  cases h with
  | seq h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩

private theorem execRand_seq_assoc {c₁ c₂ c₃ : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w (.seq c₁ (.seq c₂ c₃)) x m) :
    ExecRand w (.seq (.seq c₁ c₂) c₃) x m := by
  obtain ⟨m₁, m₂₃, h₁, h₂₃, rfl⟩ := execRand_seq_inv h
  have h₂ : ∀ z₁ ∈ m₁.support, ExecRand w c₂ z₁.1 (codeComp w c₂ z₁.1) := by
    intro z₁ hz₁
    obtain ⟨m₂, _, hc₂, _, _⟩ := execRand_seq_inv (h₂₃ z₁ hz₁)
    rwa [hc₂.codeComp_eq]
  have h₁₂ := ExecRand.seq h₁ h₂
  have h₃ : ∀ z ∈ (do
        let z₁ ← m₁
        let z₂ ← codeComp w c₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2)).support,
      ExecRand w c₃ z.1 (codeComp w c₃ z.1) := by
    intro z hz
    supp_cases hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    obtain ⟨m₂, m₃, hc₂, hc₃, _⟩ := execRand_seq_inv (h₂₃ z₁ hz₁)
    rw [hc₂.codeComp_eq] at hz₂
    have hc := hc₃ z₂ hz₂
    rwa [hc.codeComp_eq]
  have hres := ExecRand.seq h₁₂ h₃
  refine execRand_congr_eq hres ?_
  simp only [bind_assoc, pure_bind]
  refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
  obtain ⟨m₂, m₃, hc₂, hc₃, hm₂₃⟩ := execRand_seq_inv (h₂₃ z₁ hz₁)
  rw [hm₂₃, hc₂.codeComp_eq, bind_assoc]
  refine OracleComp.bind_congr_on_support fun z₂ hz₂ => ?_
  rw [(hc₃ z₂ hz₂).codeComp_eq, bind_assoc]
  refine OracleComp.bind_congr_on_support fun z₃ _ => ?_
  simp only [pure_bind, Nat.add_assoc]

private theorem execRandWithin_seq_assoc {c₁ c₂ c₃ : Code B r} {x : Data r} {P : Data r → Prop}
    {T R : ℕ} (h : ExecRandWithin w (.seq c₁ (.seq c₂ c₃)) x P T R) :
    ExecRandWithin w (.seq (.seq c₁ c₂) c₃) x P T R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  exact ⟨m, execRand_seq_assoc hm, hq, hsup⟩

private theorem execRandWithin_seq_det {c₁ c₂ : Code B r} {x y : Data r} {P : Data r → Prop}
    {T₁ T₂ R : ℕ} (h₁ : ExecWithin w c₁ x y T₁)
    (h₂ : ExecRandWithin w c₂ y P T₂ R) :
    ExecRandWithin w (.seq c₁ c₂) x P (T₁ + T₂) R := by
  have h := ExecRandWithin.seq (h₁.execRandWithin (P := (· = y)) rfl) (fun z hz => hz ▸ h₂)
  simpa only [Nat.zero_add] using h

/-- Lift an `ExecRand` execution with pathwise step bound `≤ T` directly into `ExecCodeDist`. -/
theorem ExecCodeDist.of_execRand_le {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} {T : ℕ}
    (h : ExecRand w c x m) (hT : ∀ z ∈ m.support, z.2 ≤ T) :
    ExecCodeDist w c x (m.eval.map Prod.fst) T := by
  have hle : ProbComp.expect m (fun z => (z.2 : ℝ≥0∞)) ≤ T :=
    (ProbComp.expect_mono_on_support fun z hz => Nat.cast_le.mpr (hT z hz)).trans_eq
      (ProbComp.expect_const m T)
  simpa only [ProbComp.eval_map] using (ExecCodeDist.of_execRand h).mono hle

end Structural

/-! ## `WP.Rand`: weakest preconditions for `ExecRand` -/

namespace WP

/-- `WP.Rand w c x Q`: at word size `w`, the structured randomized program `c` executes cleanly
from `x` yielding some `ProbComp (Data r × ℕ)` computation `m` satisfying `Q m`. -/
def Rand (w : ℕ) (c : Code B r) (x : Data r) (Q : ProbComp (Data r × ℕ) → Prop) : Prop :=
  ∃ m, ExecRand w c x m ∧ Q m

namespace Rand

variable {w : ℕ} {c c₁ c₂ c₃ pos neg : Code B r} {cond : Cond r}
  {x y : Data r} {m : ProbComp (Data r × ℕ)} {n : ℕ}
  {Q Q' : ProbComp (Data r × ℕ) → Prop}

/-- Extract an exact `ExecRand w c x m` certificate from `WP.Rand w c x (m = ·)`. -/
theorem execRand (h : WP.Rand w c x (m = ·)) : ExecRand w c x m :=
  let ⟨_, hm, heq⟩ := h
  heq ▸ hm

/-- Extract an existential `∃ m, ExecRand w c x m ∧ Q m` from `WP.Rand w c x Q`. -/
theorem exists_execRand (h : WP.Rand w c x Q) : ∃ m, ExecRand w c x m ∧ Q m :=
  h

/-- Weaken the postcondition of `WP.Rand`. -/
theorem mono (h : WP.Rand w c x Q) (hQ : ∀ m, Q m → Q' m) : WP.Rand w c x Q' :=
  let ⟨m, hm, hQm⟩ := h
  ⟨m, hm, hQ m hQm⟩

/-- Continue from an explicit `ExecRand` execution of `c`. -/
theorem of_execRand (h : ExecRand w c x m) (hQ : Q m) : WP.Rand w c x Q :=
  ⟨m, h, hQ⟩

/-- Continue from an exact deterministic `Exec` execution of `c`. -/
theorem of_exec (h : Exec w c x y n) (hQ : Q (pure (y, n))) : WP.Rand w c x Q :=
  ⟨pure (y, n), h.execRand, hQ⟩

/-- Lift a deterministic `WP.Exact` specification into `WP.Rand`. -/
theorem of_wp_exact (h : WP.Exact w c x fun y n => Q (pure (y, n))) : WP.Rand w c x Q :=
  let ⟨y, n, he, hQ⟩ := h
  ⟨pure (y, n), he.execRand, hQ⟩

/-- Continue from a renamed `ExecRand` execution at a leaf `c.rename f`. -/
theorem of_execRand_rename {f : Fin r → Fin r'} (hf : f.Injective)
    {c : Code B r} {x : Data r'} {m : ProbComp (Data r × ℕ)}
    {Q : ProbComp (Data r' × ℕ) → Prop}
    (h : ExecRand w c (x.comap f) m)
    (hQ : Q ((fun z => (z.1.extend f x, z.2)) <$> m)) :
    WP.Rand w (c.rename f) x Q :=
  ⟨_, h.rename hf, hQ⟩

/-- Reassociate a left-nested `.seq (.seq c₁ c₂) c₃` to `.seq c₁ (.seq c₂ c₃)`. -/
theorem seq_assoc (h : WP.Rand w (.seq c₁ (.seq c₂ c₃)) x Q) :
    WP.Rand w (.seq (.seq c₁ c₂) c₃) x Q :=
  let ⟨m, hm, hQ⟩ := h
  ⟨m, execRand_seq_assoc hm, hQ⟩

/-- Execute a deterministic prefix `c₁` via `WP.Exact`, shifting the step count of `c₂`. -/
theorem seq_exact (h : WP.Exact w c₁ x fun y n₁ =>
    WP.Rand w c₂ y fun m₂ => Q ((fun z => (z.1, n₁ + z.2)) <$> m₂)) :
    WP.Rand w (.seq c₁ c₂) x Q :=
  let ⟨_, _, he₁, _, he₂, hQ⟩ := h
  ⟨_, he₁.seqRand he₂, hQ⟩

/-- Consume a proved deterministic `Exec` contract at the head of `.seq c₁ c₂`. -/
theorem seq_of_exec (h₁ : Exec w c₁ x y n)
    (h₂ : WP.Rand w c₂ y fun m₂ => Q ((fun z => (z.1, n + z.2)) <$> m₂)) :
    WP.Rand w (.seq c₁ c₂) x Q :=
  let ⟨_, hm₂, hQ⟩ := h₂
  ⟨_, h₁.seqRand hm₂, hQ⟩

/-- Consume an existential deterministic `Exec` contract at the head of `.seq c₁ c₂`. -/
theorem seq_of_exec_spec {P : Data r → Prop} (h₁ : ∃ y, Exec w c₁ x y n ∧ P y)
    (h₂ : ∀ y, P y → WP.Rand w c₂ y fun m₂ => Q ((fun z => (z.1, n + z.2)) <$> m₂)) :
    WP.Rand w (.seq c₁ c₂) x Q :=
  let ⟨y, he₁, hP⟩ := h₁
  seq_of_exec he₁ (h₂ y hP)

/-- Consume an explicit `ExecRand` contract at the head of `.seq c₁ c₂`, exposing `(y, n)` in
`m₁.support` so `m₂` unifies by higher-order pattern matching. -/
theorem seq_of_execRand {m₁ : ProbComp (Data r × ℕ)} {m₂ : Data r → ProbComp (Data r × ℕ)}
    (h₁ : ExecRand w c₁ x m₁)
    (h₂ : ∀ y n, (y, n) ∈ m₁.support → WP.Rand w c₂ y (m₂ y = ·))
    (hQ : Q (do let z₁ ← m₁; let z₂ ← m₂ z₁.1; pure (z₂.1, z₁.2 + z₂.2))) :
    WP.Rand w (.seq c₁ c₂) x Q :=
  ⟨_, ExecRand.seq h₁ (fun z hz => (h₂ z.1 z.2 hz).execRand), hQ⟩

/-- Consume a renamed deterministic `Exec` execution at the head of `.seq (c₁.rename f) c₂`. -/
theorem seq_of_exec_rename {f : Fin r → Fin r'} (hf : f.Injective)
    {c₁ : Code B r} {c₂ : Code B r'} {x : Data r'} {y : Data r} {n : ℕ}
    {Q : ProbComp (Data r' × ℕ) → Prop}
    (h₁ : Exec w c₁ (x.comap f) y n)
    (h₂ : WP.Rand w c₂ (y.extend f x) fun m₂ => Q ((fun z => (z.1, n + z.2)) <$> m₂)) :
    WP.Rand w (.seq (c₁.rename f) c₂) x Q :=
  seq_of_exec (h₁.rename hf) h₂

/-- Consume a renamed `ExecRand` execution at the head of `.seq (c₁.rename f) c₂`, indexing `m₂`
directly by the inner state `y : Data r` so `m₂` unifies without `comap`/`extend` inversions. -/
theorem seq_of_execRand_rename {f : Fin r → Fin r'} (hf : f.Injective)
    {c₁ : Code B r} {c₂ : Code B r'} {x : Data r'}
    {m₁ : ProbComp (Data r × ℕ)} {m₂ : Data r → ProbComp (Data r' × ℕ)}
    {Q : ProbComp (Data r' × ℕ) → Prop}
    (h₁ : ExecRand w c₁ (x.comap f) m₁)
    (h₂ : ∀ y n, (y, n) ∈ m₁.support → WP.Rand w c₂ (y.extend f x) (m₂ y = ·))
    (hQ : Q (do
      let z₁ ← m₁
      let z₂ ← m₂ z₁.1
      pure (z₂.1, z₁.2 + z₂.2))) :
    WP.Rand w (.seq (c₁.rename f) c₂) x Q := by
  have hseq := ExecRand.seq (h₁.rename hf) (m₂ := fun d => m₂ (d.comap f)) fun z hz => by
    supp_cases hz with ⟨z₁, hz₁, rfl⟩
    rw [Data.comap_extend hf]
    exact (h₂ z₁.1 z₁.2 hz₁).execRand
  refine ⟨_, execRand_congr_eq hseq ?_, hQ⟩
  simp only [← bind_pure_comp, bind_assoc, pure_bind, Data.comap_extend hf]

/-- A leaf `Code.rand dst src` instruction with the bound register named in closed form. -/
theorem rand {dst src : Fin r} {a : ℕ} (hs : x.regs src = a) (hfit : Fits w a)
    (h : Q (do let k ← ProbComp.unifFin a; pure (x.set dst k.val, 1))) :
    WP.Rand (B := B) w (.rand dst src) x Q := by
  have hr : ExecRand (B := B) w (.rand dst src) x (do
      let k ← ProbComp.unifFin a
      pure (x.set dst k.val, 1)) := by
    have h0 := ExecRand.rand (B := B) (dst := dst) (src := src) (hs ▸ hfit)
    rwa [hs] at h0
  exact ⟨_, hr, h⟩

/-- A `Code.rand dst src` instruction followed by a `WP.Rand` continuation `c₂`. -/
theorem seq_rand {dst src : Fin r} {a : ℕ}
    (hs : x.regs src = a) (hfit : Fits w a)
    {m₂ : Fin (a + 1) → ProbComp (Data r × ℕ)}
    (h₂ : ∀ k : Fin (a + 1), WP.Rand w c₂ (x.set dst k.val) (m₂ k = ·))
    (h : Q (do let k ← ProbComp.unifFin a; let z₂ ← m₂ k; pure (z₂.1, 1 + z₂.2))) :
    WP.Rand w (.seq (.rand dst src) c₂) x Q :=
  ⟨_, execRand_rand_seq hs hfit (fun k => (h₂ k).execRand), h⟩

/-- A `Code.rand dst src` instruction followed by a deterministic `Exec` continuation `c₂`. -/
theorem seq_rand_det {dst src : Fin r} {a : ℕ}
    (hs : x.regs src = a) (hfit : Fits w a)
    {f : Fin (a + 1) → Data r} {n : Fin (a + 1) → ℕ}
    (h₂ : ∀ k : Fin (a + 1), Exec w c₂ (x.set dst k.val) (f k) (n k))
    (h : Q (do let k ← ProbComp.unifFin a; pure (f k, 1 + n k))) :
    WP.Rand w (.seq (.rand dst src) c₂) x Q := by
  refine ⟨_, execRand_rand_seq hs hfit (m₂ := fun k => pure (f k, n k))
    (fun k => (h₂ k).execRand), ?_⟩
  simpa only [pure_bind] using h

/-- A conditional on `cond.Holds x`, by cases. -/
theorem branch
    (hpos : cond.Holds x → WP.Rand w pos x fun m => Q ((fun z => (z.1, z.2 + 1)) <$> m))
    (hneg : ¬cond.Holds x → WP.Rand w neg x fun m => Q ((fun z => (z.1, z.2 + 2)) <$> m)) :
    WP.Rand w (.branch cond pos neg) x Q := by
  by_cases hc : cond.Holds x
  · obtain ⟨m, hm, hQ⟩ := hpos hc
    exact ⟨_, .branch_pos hc hm, hQ⟩
  · obtain ⟨m, hm, hQ⟩ := hneg hc
    exact ⟨_, .branch_neg hc hm, hQ⟩

/-- A conditional on `x.regs i < x.regs j`, with the compared values in closed form. -/
theorem branch_lt {i j : Fin r} {a b : ℕ} (hi : x.regs i = a) (hj : x.regs j = b)
    (hpos : a < b → WP.Rand w pos x fun m => Q ((fun z => (z.1, z.2 + 1)) <$> m))
    (hneg : ¬a < b → WP.Rand w neg x fun m => Q ((fun z => (z.1, z.2 + 2)) <$> m)) :
    WP.Rand w (.branch (.lt i j) pos neg) x Q :=
  branch (fun hc => hpos (hi ▸ hj ▸ hc)) (fun hc => hneg (hi ▸ hj ▸ hc))

/-- A conditional on `x.regs i = x.regs j`, with the compared values in closed form. -/
theorem branch_eq {i j : Fin r} {a b : ℕ} (hi : x.regs i = a) (hj : x.regs j = b)
    (hpos : a = b → WP.Rand w pos x fun m => Q ((fun z => (z.1, z.2 + 1)) <$> m))
    (hneg : ¬a = b → WP.Rand w neg x fun m => Q ((fun z => (z.1, z.2 + 2)) <$> m)) :
    WP.Rand w (.branch (.eq i j) pos neg) x Q :=
  branch (fun hc => hpos (hi ▸ hj ▸ hc)) (fun hc => hneg (hi ▸ hj ▸ hc))

end Rand

/-! ## `WP.RandWithin`: weakest preconditions for `ExecRandWithin` -/

/-- `WP.RandWithin w c x P Q`: at word size `w`, the structured randomized program `c` terminates
cleanly from `x` achieving postcondition `P` within some step bound `t` and `rand`-call bound `q`
satisfying `Q t q`. -/
def RandWithin (w : ℕ) (c : Code B r) (x : Data r) (P : Data r → Prop)
    (Q : ℕ → ℕ → Prop) : Prop :=
  ∃ t q, ExecRandWithin w c x P t q ∧ Q t q

namespace RandWithin

variable {w : ℕ} {c c₁ c₂ c₃ pos neg : Code B r} {cond : Cond r}
  {x y : Data r} {P P₁ : Data r → Prop} {T R T₁ R₁ T₂ R₂ : ℕ}
  {Q : ℕ → ℕ → Prop}

/-- Extract `ExecRandWithin w c x P T R`. -/
theorem execRandWithin (h : WP.RandWithin w c x P fun t q => t ≤ T ∧ q ≤ R) :
    ExecRandWithin w c x P T R :=
  let ⟨_, _, he, ht, hq⟩ := h
  he.mono (fun _ hx => hx) ht hq

/-- Continue from an explicit `ExecRandWithin` certificate. -/
theorem of_execRandWithin (h : ExecRandWithin w c x P₁ T₁ R₁) (hP : ∀ y, P₁ y → P y)
    (hQ : Q T₁ R₁) : WP.RandWithin w c x P Q :=
  ⟨T₁, R₁, h.mono hP le_rfl le_rfl, hQ⟩

/-- Lift a deterministic `WP` execution into `WP.RandWithin` (`0` `rand` calls). -/
theorem of_wp (h : WP w c x fun y t => P y ∧ Q t 0) : WP.RandWithin w c x P Q :=
  let ⟨_, t, he, hP, hQ⟩ := h
  ⟨t, 0, he.execRandWithin hP, hQ⟩

/-- Lift a deterministic `ExecWithin` specification into `WP.RandWithin`. -/
theorem of_execWithin (h : ExecWithin w c x y T₁) (hP : P y) (hQ : Q T₁ 0) :
    WP.RandWithin w c x P Q :=
  ⟨T₁, 0, h.execRandWithin hP, hQ⟩

/-- Continue from an explicit `ExecRandWithin` contract renamed via an injective register map. -/
theorem of_execRandWithin_rename {f : Fin r → Fin r'} (hf : f.Injective)
    {c : Code B r} {x : Data r'} {P : Data r' → Prop} {P₁ : Data r → Prop}
    {T₁ R₁ : ℕ} {Q : ℕ → ℕ → Prop}
    (h : ExecRandWithin w c (x.comap f) P₁ T₁ R₁)
    (hP : ∀ y, P₁ y → P (y.extend f x)) (hQ : Q T₁ R₁) :
    WP.RandWithin w (c.rename f) x P Q :=
  ⟨T₁, R₁, (h.rename hf).mono (fun _ ⟨y, hy, heq⟩ => heq ▸ hP y hy) le_rfl le_rfl, hQ⟩

/-- Reassociate left-nested sequencing. -/
theorem seq_assoc (h : WP.RandWithin w (.seq c₁ (.seq c₂ c₃)) x P Q) :
    WP.RandWithin w (.seq (.seq c₁ c₂) c₃) x P Q :=
  let ⟨t, q, he, hQ⟩ := h
  ⟨t, q, execRandWithin_seq_assoc he, hQ⟩

/-- Execute a deterministic prefix `c₁` via `WP`, adding its step count to the continuation. -/
theorem seq_wp (h : WP w c₁ x fun y t₁ =>
    WP.RandWithin w c₂ y P fun t₂ q => Q (t₂ + t₁) q) :
    WP.RandWithin w (.seq c₁ c₂) x P Q :=
  let ⟨_, t₁, he₁, t₂, q, he₂, hQ⟩ := h
  ⟨t₁ + t₂, q, execRandWithin_seq_det he₁ he₂, Nat.add_comm t₁ t₂ ▸ hQ⟩

/-- Consume a deterministic `ExecWithin` at the head of `.seq c₁ c₂`. -/
theorem seq_of_execWithin (h₁ : ExecWithin w c₁ x y T₁)
    (h₂ : WP.RandWithin w c₂ y P fun t₂ q => Q (t₂ + T₁) q) :
    WP.RandWithin w (.seq c₁ c₂) x P Q :=
  seq_wp (WP.of_execWithin h₁ h₂)

/-- Consume an existential deterministic `ExecWithin` contract at the head of `.seq c₁ c₂`. -/
theorem seq_of_execWithin_spec (h₁ : ∃ y, ExecWithin w c₁ x y T₁ ∧ P₁ y)
    (h₂ : ∀ y, P₁ y → WP.RandWithin w c₂ y P fun t₂ q => Q (t₂ + T₁) q) :
    WP.RandWithin w (.seq c₁ c₂) x P Q :=
  let ⟨y, he₁, hP₁⟩ := h₁
  seq_of_execWithin he₁ (h₂ y hP₁)

/-- Consume a deterministic `Exec` contract at the head of `.seq c₁ c₂`. -/
theorem seq_of_exec (h₁ : Exec w c₁ x y T₁)
    (h₂ : WP.RandWithin w c₂ y P fun t₂ q => Q (t₂ + T₁) q) :
    WP.RandWithin w (.seq c₁ c₂) x P Q :=
  seq_of_execWithin h₁.within h₂

/-- Consume a randomized `ExecRandWithin` contract at the head of `.seq c₁ c₂`. -/
theorem seq_of_execRandWithin (h₁ : ExecRandWithin w c₁ x P₁ T₁ R₁)
    (h₂ : ∀ y, P₁ y → WP.RandWithin w c₂ y P fun t₂ q₂ => t₂ ≤ T₂ ∧ q₂ ≤ R₂)
    (hQ : Q (T₁ + T₂) (R₁ + R₂)) :
    WP.RandWithin w (.seq c₁ c₂) x P Q :=
  ⟨T₁ + T₂, R₁ + R₂, h₁.seq (fun y hy => (h₂ y hy).execRandWithin), hQ⟩

/-- A leaf `Code.rand dst src` instruction. -/
theorem rand {dst src : Fin r} {a : ℕ} (hs : x.regs src = a) (hfit : Fits w a)
    (hP : ∀ k : Fin (a + 1), P (x.set dst k.val)) (hQ : Q 1 1) :
    WP.RandWithin (B := B) w (.rand dst src) x P Q :=
  ⟨1, 1, ExecRandWithin.rand (hs ▸ hfit) fun k => hP ⟨k.val, hs ▸ k.isLt⟩, hQ⟩

/-- A `Code.rand dst src` instruction followed by a `WP.RandWithin` continuation. -/
theorem seq_rand {dst src : Fin r} {a : ℕ} (hs : x.regs src = a) (hfit : Fits w a)
    (h₂ : ∀ k : Fin (a + 1), WP.RandWithin w c₂ (x.set dst k.val) P fun t₂ q₂ =>
      t₂ ≤ T₂ ∧ q₂ ≤ R₂)
    (hQ : Q (1 + T₂) (1 + R₂)) :
    WP.RandWithin (B := B) w (.seq (.rand dst src) c₂) x P Q := by
  refine ⟨1 + T₂, 1 + R₂, (ExecRandWithin.rand (P := fun d => ∃ k : Fin (a + 1),
    d = x.set dst k.val) (hs ▸ hfit) fun k => ⟨⟨k.val, hs ▸ k.isLt⟩, rfl⟩).seq ?_, hQ⟩
  rintro _ ⟨k, rfl⟩
  exact (h₂ k).execRandWithin

/-- Conditional on `cond.Holds x`. -/
theorem branch
    (hpos : cond.Holds x → WP.RandWithin w pos x P fun t q => Q (t + 1) q)
    (hneg : ¬cond.Holds x → WP.RandWithin w neg x P fun t q => Q (t + 2) q) :
    WP.RandWithin w (.branch cond pos neg) x P Q := by
  by_cases hc : cond.Holds x
  · obtain ⟨t, q, he, hQ⟩ := hpos hc
    exact ⟨t + 1, q, he.branch_pos hc, hQ⟩
  · obtain ⟨t, q, he, hQ⟩ := hneg hc
    exact ⟨t + 2, q, he.branch_neg hc, hQ⟩

/-- Conditional on `x.regs i < x.regs j`. -/
theorem branch_lt {i j : Fin r} {a b : ℕ} (hi : x.regs i = a) (hj : x.regs j = b)
    (hpos : a < b → WP.RandWithin w pos x P fun t q => Q (t + 1) q)
    (hneg : ¬a < b → WP.RandWithin w neg x P fun t q => Q (t + 2) q) :
    WP.RandWithin w (.branch (.lt i j) pos neg) x P Q :=
  branch (fun hc => hpos (hi ▸ hj ▸ hc)) (fun hc => hneg (hi ▸ hj ▸ hc))

/-- Conditional on `x.regs i = x.regs j`. -/
theorem branch_eq {i j : Fin r} {a b : ℕ} (hi : x.regs i = a) (hj : x.regs j = b)
    (hpos : a = b → WP.RandWithin w pos x P fun t q => Q (t + 1) q)
    (hneg : ¬a = b → WP.RandWithin w neg x P fun t q => Q (t + 2) q) :
    WP.RandWithin w (.branch (.eq i j) pos neg) x P Q :=
  branch (fun hc => hpos (hi ▸ hj ▸ hc)) (fun hc => hneg (hi ▸ hj ▸ hc))

end RandWithin

/-! ## `WP.Dist`: weakest preconditions for `ExecCodeDist` -/

/-- `WP.Dist w c x Q`: at word size `w`, the structured randomized program `c` executes cleanly
from `x` with exit distribution `μ : PMF (Data r)` and expected instruction bound `T : ℝ≥0∞`
satisfying `Q μ T`. -/
def Dist (w : ℕ) (c : Code B r) (x : Data r) (Q : PMF (Data r) → ℝ≥0∞ → Prop) : Prop :=
  ∃ μ T, ExecCodeDist w c x μ T ∧ Q μ T

namespace Dist

variable {w : ℕ} {c c₁ c₂ pos neg : Code B r} {cond : Cond r}
  {x y : Data r} {μ μ₁ : PMF (Data r)} {T T₁ : ℝ≥0∞} {n : ℕ}
  {Q Q' : PMF (Data r) → ℝ≥0∞ → Prop}

/-- Extract `ExecCodeDist w c x μ T`. -/
theorem execCodeDist (h : WP.Dist w c x fun μ' T' => μ = μ' ∧ T' ≤ T) :
    ExecCodeDist w c x μ T :=
  let ⟨_, _, he, hμ, hT⟩ := h
  he.congr_dist hμ.symm hT

/-- Weaken the postcondition of `WP.Dist`. -/
theorem mono (h : WP.Dist w c x Q) (hQ : ∀ μ T, Q μ T → Q' μ T) : WP.Dist w c x Q' :=
  let ⟨μ, T, he, hQm⟩ := h
  ⟨μ, T, he, hQ μ T hQm⟩

/-- Continue from an explicit `ExecCodeDist` certificate. -/
theorem of_execCodeDist (h : ExecCodeDist w c x μ T) (hQ : Q μ T) : WP.Dist w c x Q :=
  ⟨μ, T, h, hQ⟩

/-- Lift a deterministic `WP` execution into `WP.Dist`. -/
theorem of_wp (h : WP w c x fun y t => Q (PMF.pure y) t) : WP.Dist w c x Q :=
  let ⟨y, t, he, hQ⟩ := h
  ⟨PMF.pure y, t, ExecCodeDist.of_execWithin he, hQ⟩

/-- Continue from a deterministic `ExecWithin` execution. -/
theorem of_execWithin (h : ExecWithin w c x y n) (hQ : Q (PMF.pure y) n) : WP.Dist w c x Q :=
  ⟨PMF.pure y, n, ExecCodeDist.of_execWithin h, hQ⟩

/-- Continue from a deterministic `Exec` execution. -/
theorem of_exec (h : Exec w c x y n) (hQ : Q (PMF.pure y) n) : WP.Dist w c x Q :=
  ⟨PMF.pure y, n, ExecCodeDist.of_exec h, hQ⟩

/-- Continue from an `ExecRand` execution with pathwise step bound `≤ n`. -/
theorem of_execRand_le {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m)
    (hT : ∀ z ∈ m.support, z.2 ≤ n) (hQ : Q (m.eval.map Prod.fst) n) :
    WP.Dist w c x Q :=
  ⟨m.eval.map Prod.fst, n, ExecCodeDist.of_execRand_le h hT, hQ⟩

/-- Execute a deterministic prefix `c₁` via `WP`, adding its step count to the continuation. -/
theorem seq_wp (h : WP w c₁ x fun y t₁ =>
    WP.Dist w c₂ y fun μ t₂ => Q μ ((t₁ : ℝ≥0∞) + t₂)) :
    WP.Dist w (.seq c₁ c₂) x Q :=
  let ⟨_, _, he₁, _, _, he₂, hQ⟩ := h
  ⟨_, _, (ExecCodeDist.of_execWithin he₁).seq_pure he₂, hQ⟩

/-- Consume a deterministic `ExecWithin` at the head of `.seq c₁ c₂`. -/
theorem seq_of_execWithin (h₁ : ExecWithin w c₁ x y n)
    (h₂ : WP.Dist w c₂ y fun μ t₂ => Q μ ((n : ℝ≥0∞) + t₂)) :
    WP.Dist w (.seq c₁ c₂) x Q :=
  seq_wp (WP.of_execWithin h₁ h₂)

/-- Consume an existential deterministic `ExecWithin` contract at the head of `.seq c₁ c₂`. -/
theorem seq_of_execWithin_spec {P : Data r → Prop} (h₁ : ∃ y, ExecWithin w c₁ x y n ∧ P y)
    (h₂ : ∀ y, P y → WP.Dist w c₂ y fun μ t₂ => Q μ ((n : ℝ≥0∞) + t₂)) :
    WP.Dist w (.seq c₁ c₂) x Q :=
  let ⟨y, he₁, hP⟩ := h₁
  seq_of_execWithin he₁ (h₂ y hP)

/-- Consume a deterministic `Exec` contract at the head of `.seq c₁ c₂`. -/
theorem seq_of_exec (h₁ : Exec w c₁ x y n)
    (h₂ : WP.Dist w c₂ y fun μ t₂ => Q μ ((n : ℝ≥0∞) + t₂)) :
    WP.Dist w (.seq c₁ c₂) x Q :=
  seq_of_execWithin h₁.within h₂

/-- Consume an `ExecCodeDist` at the head of `.seq c₁ c₂` with a uniform continuation step bound
`B₂`, leaving a `WP.Dist` continuation so `μ₂` unifies by higher-order pattern matching. -/
theorem seq_of_execCodeDist_const {μ₂ : Data r → PMF (Data r)} {B₂ : ℝ≥0∞}
    (h₁ : ExecCodeDist w c₁ x μ₁ T₁)
    (h₂ : ∀ y ∈ μ₁.support, WP.Dist w c₂ y fun μ' T' => μ₂ y = μ' ∧ T' ≤ B₂)
    (hQ : Q (μ₁.bind μ₂) (T₁ + B₂)) :
    WP.Dist w (.seq c₁ c₂) x Q :=
  ⟨_, _, h₁.seq_const (fun y hy => (h₂ y hy).execCodeDist) (fun _ _ => le_rfl), hQ⟩

/-- A leaf `Code.rand dst src` instruction. -/
theorem rand {dst src : Fin r} {a : ℕ} (hs : x.regs src = a) (hfit : Fits w a)
    (hQ : Q ((ProbComp.unifFin a).eval.map fun k => x.set dst k.val) 1) :
    WP.Dist (B := B) w (.rand dst src) x Q := by
  have hr : ExecCodeDist (B := B) w (.rand dst src) x
      ((ProbComp.unifFin a).eval.map fun k => x.set dst k.val) 1 := by
    have h0 := ExecCodeDist.rand (B := B) (dst := dst) (src := src) (hs ▸ hfit)
    rwa [hs] at h0
  exact ⟨_, 1, hr, hQ⟩

/-- Conditional on `cond.Holds x`. -/
theorem branch
    (hpos : cond.Holds x → WP.Dist w pos x fun μ T => Q μ (T + 1))
    (hneg : ¬cond.Holds x → WP.Dist w neg x fun μ T => Q μ (T + 2)) :
    WP.Dist w (.branch cond pos neg) x Q := by
  by_cases hc : cond.Holds x
  · obtain ⟨μ, T, he, hQ⟩ := hpos hc
    exact ⟨μ, T + 1, .branch_pos hc he, hQ⟩
  · obtain ⟨μ, T, he, hQ⟩ := hneg hc
    exact ⟨μ, T + 2, .branch_neg hc he, hQ⟩

/-- Conditional on `x.regs i < x.regs j`. -/
theorem branch_lt {i j : Fin r} {a b : ℕ} (hi : x.regs i = a) (hj : x.regs j = b)
    (hpos : a < b → WP.Dist w pos x fun μ T => Q μ (T + 1))
    (hneg : ¬a < b → WP.Dist w neg x fun μ T => Q μ (T + 2)) :
    WP.Dist w (.branch (.lt i j) pos neg) x Q :=
  branch (fun hc => hpos (hi ▸ hj ▸ hc)) (fun hc => hneg (hi ▸ hj ▸ hc))

/-- Conditional on `x.regs i = x.regs j`. -/
theorem branch_eq {i j : Fin r} {a b : ℕ} (hi : x.regs i = a) (hj : x.regs j = b)
    (hpos : a = b → WP.Dist w pos x fun μ T => Q μ (T + 1))
    (hneg : ¬a = b → WP.Dist w neg x fun μ T => Q μ (T + 2)) :
    WP.Dist w (.branch (.eq i j) pos neg) x Q :=
  branch (fun hc => hpos (hi ▸ hj ▸ hc)) (fun hc => hneg (hi ▸ hj ▸ hc))

end Dist

end WP

/-! ## Randomized symbolic execution tactic (`wram_rand_exec`) -/

namespace WP.RandExec

open Lean Meta Elab Tactic

private meta inductive Kind where
  | rand
  | randWithin
  | dist
  deriving BEq

private meta def goalKind? (tgt : Expr) : Option Kind :=
  let t := tgt.consumeMData
  if t.isAppOfArity ``WP.Rand 6 then some .rand
  else if t.isAppOfArity ``WP.RandWithin 7 then some .randWithin
  else if t.isAppOfArity ``WP.Dist 6 then some .dist
  else none

private meta def toWPRand (g : MVarId) : MetaM (MVarId × Kind × Bool) := g.withContext do
  let tgt := (WP.Exec.headBetaAll (← instantiateMVars (← g.getType))).consumeMData
  if let some k := goalKind? tgt then return (g, k, false)
  let s ← saveState
  for (rule, k, direct) in [
      (``WP.Rand.execRand, Kind.rand, true),
      (``WP.RandWithin.execRandWithin, Kind.randWithin, true),
      (``WP.Dist.execCodeDist, Kind.dist, true),
      (``WP.Rand.exists_execRand, Kind.rand, false)] do
    try
      let [g'] ← g.apply (← mkConstWithFreshMVarLevels rule) | failure
      return (g', k, direct)
    catch _ => s.restore
  throwError "wram_rand_exec: expected a goal `ExecRand w c x m`, `∃ m, ExecRand w c x m ∧ P m`, \
    `WP.Rand w c x Q`, `ExecRandWithin w c x P T R`, `WP.RandWithin w c x P Q`, \
    `ExecCodeDist w c x μ T`, or `WP.Dist w c x Q`, got{indentExpr tgt}"

private meta def stepBranch (cfg : WP.Exec.Config) (g : MVarId) (rule : Name)
    (walkCont : MVarId → TacticM (Array MVarId)) : TacticM (Array MVarId) := do
  let tag ← g.getTag
  let saved ← saveState
  let args ← WP.Exec.applyRule cfg g rule
  for (n, arg) in args do
    if n == `hi || n == `hj then
      let ty ← instantiateMVars (← inferType arg)
      let some (_, lhs, rhs) := ty.eq?
        | throwError "wram_rand_exec: unexpected premise of `{rule}`"
      WP.Exec.evalPremise cfg arg lhs rhs
  let some hpos := args.find? (·.1 == `hpos) |>.map (·.2) | throwError "wram_rand_exec: no `hpos`"
  let some hneg := args.find? (·.1 == `hneg) |>.map (·.2) | throwError "wram_rand_exec: no `hneg`"
  let .forallE _ cond _ _ ← instantiateMVars (← inferType hpos)
    | throwError "wram_rand_exec: unexpected premise of `{rule}`"
  let take (keep drop : Expr) (contra : Expr → Expr) : TacticM (Array MVarId) := do
    let .forallE _ dom body _ ← instantiateMVars (← inferType keep)
      | throwError "wram_rand_exec: unexpected premise of `{rule}`"
    let .forallE _ ndom nbody _ ← instantiateMVars (← inferType drop)
      | throwError "wram_rand_exec: unexpected premise of `{rule}`"
    drop.mvarId!.assign (← withLocalDeclD `hc ndom fun hc => do
      mkLambdaFVars #[hc] (← mkFalseElim nbody (contra hc)))
    let k ← mkFreshExprSyntheticOpaqueMVar (WP.Exec.headBetaAll body) tag
    keep.mvarId!.assign (.lam `hc dom k .default)
    walkCont k.mvarId!
  match (← WP.Exec.tryProve cfg (WP.Exec.closesWith cfg.disch) cond).1 with
  | some p => take hpos hneg fun hc => mkApp hc p
  | none =>
    match (← WP.Exec.tryProve cfg (WP.Exec.closesWith cfg.disch) (mkNot cond)).1 with
    | some np => take hneg hpos fun hc => mkApp np hc
    | none =>
      unless cfg.split do
        saved.restore
        cfg.steps.modify (· - 1)
        return #[g]
      let (_, gpos) ← (← WP.Exec.premiseGoal hpos (tag ++ `pos)).intro `hc
      let (_, gneg) ← (← WP.Exec.premiseGoal hneg (tag ++ `neg)).intro `hc
      return (← walkCont gpos) ++ (← walkCont gneg)

private meta partial def isKnownDetOp (code : Expr) : MetaM Bool := do
  let code ← whnfR code
  match code.getAppFn.constName? with
  | some ``Code.op => return (WP.Exec.opRule? (code.getArg! 2)).isSome
  | some ``Code.seq =>
    return (← isKnownDetOp (code.getArg! 2)) && (← isKnownDetOp (code.getArg! 3))
  | _ => return false

private meta def stepRandLeaf (cfg : WP.Exec.Config) (g : MVarId) (rule : Name) :
    TacticM (Array MVarId) := do
  let tag ← g.getTag
  let args ← WP.Exec.applyRule cfg g rule
  let mut hs? := none
  let mut hfit? := none
  let mut conts : Array MVarId := #[]
  for (n, arg) in args do
    if ← arg.mvarId!.isAssigned then continue
    let ty ← instantiateMVars (← inferType arg)
    unless ← isProp ty do continue
    if n == `hs then hs? := some arg
    else if n == `hfit then hfit? := some arg
    else conts := conts.push (← WP.Exec.premiseGoal arg tag)
  if let some hs := hs? then
    let ty ← instantiateMVars (← inferType hs)
    let some (_, lhs, rhs) := ty.eq? | throwError "wram_rand_exec: unexpected `hs` premise"
    WP.Exec.evalPremise cfg hs lhs rhs
  if let some hfit := hfit? then
    WP.Exec.sidePremise cfg `hfit hfit
  return conts

private meta def trySeqRandDet (cfg : WP.Exec.Config) (g : MVarId) :
    TacticM (Option (Array MVarId)) := do
  let tag ← g.getTag
  let saved ← saveState
  let stepsBefore ← cfg.steps.get
  let sideBefore ← cfg.sideGoals.get
  try
    let args ← WP.Exec.applyRule cfg g ``WP.Rand.seq_rand_det
    let some hs := args.find? (·.1 == `hs) |>.map (·.2) | failure
    let some hfit := args.find? (·.1 == `hfit) |>.map (·.2) | failure
    let some h2 := args.find? (·.1 == `h₂) |>.map (·.2) | failure
    let some hcont := args.find? (·.1 == `h) |>.map (·.2) | failure
    let some fArg := args.find? (·.1 == `f) |>.map (·.2) | failure
    let some nArg := args.find? (·.1 == `n) |>.map (·.2) | failure
    let ty ← instantiateMVars (← inferType hs)
    let some (_, lhs, rhs) := ty.eq? | failure
    WP.Exec.evalPremise cfg hs lhs rhs
    WP.Exec.sidePremise cfg `hfit hfit
    let h2Ty ← instantiateMVars (← inferType h2)
    let .forallE kName kDom body _ := h2Ty | failure
    withLocalDeclD kName kDom fun k => do
      let bodyInst := body.instantiate1 k
      let_expr Exec B r w c₂ xk _fk _nk := bodyInst | failure
      let fkM ← mkFreshExprMVar (← mkAppM ``Data #[r])
      let nkM ← mkFreshExprMVar (mkConst ``Nat)
      let goalType ← mkAppOptM ``Exec
        #[some B, some r, some w, some c₂, some xk, some fkM, some nkM]
      let gExec ← mkFreshExprSyntheticOpaqueMVar goalType tag
      let (gWP, _, _) ← WP.Exec.toWP gExec.mvarId!
      let leaves ← WP.Exec.walk cfg gWP
      if leaves.size != 1 then failure
      let leaf := leaves[0]!
      leaf.withContext do
        let ltgt := (← instantiateMVars (← leaf.getType)).consumeMData
        let some (tEq, yEq) := ltgt.and? | failure
        let some (_, tVal, _) := tEq.eq? | failure
        let some (_, yVal, _) := yEq.eq? | failure
        unless ← isDefEq nkM tVal do failure
        unless ← isDefEq fkM yVal do failure
        leaf.assign (← mkAppM ``And.intro #[← mkEqRefl tVal, ← mkEqRefl yVal])
      unless ← isDefEq fArg (← mkLambdaFVars #[k] (← instantiateMVars fkM)) do failure
      unless ← isDefEq nArg (← mkLambdaFVars #[k] (← instantiateMVars nkM)) do failure
      h2.mvarId!.assign (← mkLambdaFVars #[k] (← instantiateMVars gExec))
    return some #[← WP.Exec.premiseGoal hcont tag]
  catch _ =>
    saved.restore
    cfg.steps.set stepsBefore
    cfg.sideGoals.set sideBefore
    return none

private meta def stepSeqRandWP (cfg : WP.Exec.Config) (g : MVarId) (rule : Name)
    (walkCont : MVarId → TacticM (Array MVarId)) : TacticM (Array MVarId) := do
  let tag ← g.getTag
  let args ← WP.Exec.applyRule cfg g rule
  let some hs := args.find? (·.1 == `hs) |>.map (·.2)
    | throwError "wram_rand_exec: missing `hs` in `{rule}`"
  let some hfit := args.find? (·.1 == `hfit) |>.map (·.2)
    | throwError "wram_rand_exec: missing `hfit` in `{rule}`"
  let some h2 := args.find? (·.1 == `h₂) |>.map (·.2)
    | throwError "wram_rand_exec: missing `h₂` in `{rule}`"
  let some hcont := ((args.find? (·.1 == `h)) <|> (args.find? (·.1 == `hQ))).map (·.2)
    | throwError "wram_rand_exec: missing continuation in `{rule}`"
  let ty ← instantiateMVars (← inferType hs)
  let some (_, lhs, rhs) := ty.eq? | throwError "wram_rand_exec: unexpected `hs` premise"
  WP.Exec.evalPremise cfg hs lhs rhs
  WP.Exec.sidePremise cfg `hfit hfit
  let (_, g2) ← (← WP.Exec.premiseGoal h2 (tag ++ `rand)).intro `k
  let gCont ← WP.Exec.premiseGoal hcont tag
  return (← walkCont g2) ++ #[gCont]

private meta partial def walk (cfg : WP.Exec.Config) (g : MVarId) : TacticM (Array MVarId) :=
    g.withContext do
  let tgt := WP.Exec.headBetaAll (← instantiateMVars (← g.getType))
  let g ← g.replaceTargetDefEq tgt
  let tgt := tgt.consumeMData
  let some kind := goalKind? tgt | return #[g]
  let code ← whnfR (tgt.getArg! 3)
  let tag ← g.getTag
  match code.getAppFn.constName? with
  | some ``Code.seq =>
    let c1 ← whnfR (code.getArg! 2)
    let c2 := code.getArg! 3
    match c1.getAppFn.constName? with
    | some ``Code.seq =>
      match kind with
      | .rand =>
        let args ← WP.Exec.applyRule cfg g ``WP.Rand.seq_assoc
        let some h := args.find? (·.1 == `h) |>.map (·.2)
          | throwError "wram_rand_exec: missing `h` in `seq_assoc`"
        walk cfg (← WP.Exec.premiseGoal h tag)
      | .randWithin =>
        let args ← WP.Exec.applyRule cfg g ``WP.RandWithin.seq_assoc
        let some h := args.find? (·.1 == `h) |>.map (·.2)
          | throwError "wram_rand_exec: missing `h` in `seq_assoc`"
        walk cfg (← WP.Exec.premiseGoal h tag)
      | .dist =>
        unless ← isKnownDetOp c1 do return #[g]
        let args ← WP.Exec.applyRule cfg g ``WP.Dist.seq_wp
        let some h := args.find? (·.1 == `h) |>.map (·.2)
          | throwError "wram_rand_exec: missing `h` in `WP.Dist.seq_wp`"
        let gs ← WP.Exec.walk cfg (← WP.Exec.premiseGoal h tag)
        let mut out : Array MVarId := #[]
        for g' in gs do
          out := out ++ (← walk cfg g')
        return out
    | some ``Code.op =>
      if (WP.Exec.opRule? (c1.getArg! 2)).isNone then return #[g]
      let seqRule := match kind with
        | .rand => ``WP.Rand.seq_exact
        | .randWithin => ``WP.RandWithin.seq_wp
        | .dist => ``WP.Dist.seq_wp
      let args ← WP.Exec.applyRule cfg g seqRule
      let some h := args.find? (·.1 == `h) |>.map (·.2)
        | throwError "wram_rand_exec: missing `h` in `{seqRule}`"
      let gs ← WP.Exec.walk cfg (← WP.Exec.premiseGoal h tag)
      let mut out : Array MVarId := #[]
      for g' in gs do
        out := out ++ (← walk cfg g')
      return out
    | some ``Code.rand =>
      match kind with
      | .rand =>
        if ← isKnownDetOp c2 then
          if let some out ← trySeqRandDet cfg g then
            return out
        stepSeqRandWP cfg g ``WP.Rand.seq_rand (walk cfg)
      | .randWithin =>
        stepSeqRandWP cfg g ``WP.RandWithin.seq_rand (walk cfg)
      | .dist => return #[g]
    | _ => return #[g]
  | some ``Code.op =>
    if (WP.Exec.opRule? (code.getArg! 2)).isNone then return #[g]
    let leafRule := match kind with
      | .rand => ``WP.Rand.of_wp_exact
      | .randWithin => ``WP.RandWithin.of_wp
      | .dist => ``WP.Dist.of_wp
    let args ← WP.Exec.applyRule cfg g leafRule
    let some h := args.find? (·.1 == `h) |>.map (·.2)
      | throwError "wram_rand_exec: missing `h` in `{leafRule}`"
    WP.Exec.walk cfg (← WP.Exec.premiseGoal h tag)
  | some ``Code.rand =>
    let randRule := match kind with
      | .rand => ``WP.Rand.rand
      | .randWithin => ``WP.RandWithin.rand
      | .dist => ``WP.Dist.rand
    stepRandLeaf cfg g randRule
  | some ``Code.branch =>
    let condName := (code.getArg! 2).getAppFn.constName?
    match kind, condName with
    | .rand, some ``Cond.lt => stepBranch cfg g ``WP.Rand.branch_lt (walk cfg)
    | .rand, some ``Cond.eq => stepBranch cfg g ``WP.Rand.branch_eq (walk cfg)
    | .randWithin, some ``Cond.lt => stepBranch cfg g ``WP.RandWithin.branch_lt (walk cfg)
    | .randWithin, some ``Cond.eq => stepBranch cfg g ``WP.RandWithin.branch_eq (walk cfg)
    | .dist, some ``Cond.lt => stepBranch cfg g ``WP.Dist.branch_lt (walk cfg)
    | .dist, some ``Cond.eq => stepBranch cfg g ``WP.Dist.branch_eq (walk cfg)
    | _, _ => return #[g]
  | _ => return #[g]

private meta def closesQuiet (tac : TSyntax `tactic) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    if (← withoutRecover (evalTacticAt tac g)).isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

private meta def tryClosePost (kind : Kind) (g : MVarId) : TacticM (Option MVarId) :=
    g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  if (goalKind? tgt).isSome then return some g
  match kind with
  | .rand =>
    if let some (_, lhs, rhs) := tgt.eq? then
      if lhs.getAppFn.isMVar && rhs.getAppFn.isMVar then return some g
    else return some g
    let tac ← `(tactic|
      (first
        | rfl
        | (simp only [← bind_pure_comp, bind_assoc, pure_bind, map_pure, Functor.map_map,
            Function.comp_def, Nat.add_assoc, Cslib.WordRAM.Data.set_regs_self]
           <;> try rfl)))
    if ← closesQuiet tac g then return none
    return some g
  | .randWithin =>
    let tac ← `(tactic| omega)
    if ← closesQuiet tac g then return none
    return some g
  | .dist =>
    if let some (eqPart, _) := tgt.and? then
      if let some (_, lhs, rhs) := eqPart.eq? then
        if lhs.getAppFn.isMVar && rhs.getAppFn.isMVar then return some g
      else return some g
    else return some g
    let tac ← `(tactic|
      (refine And.intro ?_ ?_
       · first | rfl | (simp only [PMF.bind_pure, PMF.pure_bind, ← PMF.bind_pure_comp,
                          PMF.map_comp, Function.comp_def] <;> try rfl)
       · first | rfl | exact le_rfl | (try norm_cast; try omega)))
    if ← closesQuiet tac g then return none
    return some g

end WP.RandExec

/-- `wram_rand_exec` symbolically executes the straight-line, branching, and `rand` parts of a
structured randomized word-RAM program on an `ExecRand`, `WP.Rand`, `ExecRandWithin`,
`WP.RandWithin`, `ExecCodeDist`, or `WP.Dist` goal.

It reassociates left-nested `Code.seq`, collapses deterministic `.op` steps using `wram_exec`'s
simplifier and discharger, steps `Code.branch` (or splits unless `-split` is passed), and steps
`Code.rand dst src` (both as a leaf and as `.seq (.rand dst src) c₂`, introducing `k` when `c₂`
contains calls or loops). Stops cleanly at loops and unexpanded subroutines, leaving a `WP.Rand`,
`WP.RandWithin`, or `WP.Dist` goal ready for `wram_rand_call`. -/
syntax (name := wramRandExec) "wram_rand_exec" Lean.Parser.Tactic.optConfig
  (Lean.Parser.Tactic.discharger)?
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_rand_exec $cfg:optConfig $[$d?:discharger]? $[[$args,*]]?) =>
      withMainContext do
    let mut split := true
    for item in cfg.raw[0].getArgs do
      match item[0] with
      | `(Lean.Parser.Tactic.negConfigItem| -split) => split := false
      | `(Lean.Parser.Tactic.posConfigItem| +split) => split := true
      | _ => throwErrorAt item "wram_rand_exec: unknown option; the only option is `-split`"
    let userDisch ← liftMacroM <| WP.Exec.dischOf d?
    let disch ← `(tactic| ($userDisch))
    let args := args.map (·.getElems.map (·.raw)) |>.getD #[]
    WP.Exec.withSimpContext userDisch args fun ctx simprocs simpDischarge => do
      let sideGoals ← IO.mkRef #[]
      let steps ← IO.mkRef 0
      let cfg : WP.Exec.Config := { ctx, simprocs, simpDischarge, disch, sideGoals, steps, split }
      let (g, kind, _) ← WP.RandExec.toWPRand (← getMainGoal)
      let mains ← WP.RandExec.walk cfg g
      if (← cfg.steps.get) == 0 then
        let tgt ← instantiateMVars (← g.getType)
        throwError "wram_rand_exec: nothing to execute in{indentExpr tgt}\nThe program starts with \
          a loop or a named subroutine. Apply its contract with `wram_rand_call`, or unfold it."
      let mains ← mains.filterMapM (WP.RandExec.tryClosePost kind)
      replaceMainGoal (mains ++ (← cfg.sideGoals.get)).toList

/-- `wram_rand_call h` applies a proved deterministic (`Exec` / `ExecWithin`) or randomized
(`ExecRand` / `ExecRandWithin` / `ExecCodeDist`) contract `h` at the head of a `WP.Rand`,
`WP.RandWithin`, or `WP.Dist` goal (either a leaf call `c` or a sequenced call `.seq c₁ c₂`),
and exposes the continuation. Pass `renamed hf` to lift a contract across `Code.rename f` via
`hf : f.Injective`. -/
syntax (name := wramRandCall) "wram_rand_call " term:max : tactic

@[tactic_alt wramRandCall]
syntax (name := wramRandCallWith) "wram_rand_call " term:max " with"
  (ppSpace colGt rintroPat)+ : tactic

@[tactic_alt wramRandCall]
syntax (name := wramRandCallRenamed) "wram_rand_call " term:max &" renamed " term:max : tactic

@[tactic_alt wramRandCall]
syntax (name := wramRandCallRenamedWith) "wram_rand_call " term:max &" renamed " term:max
  " with" (ppSpace colGt rintroPat)+ : tactic

private meta def tryFirstAction (acts : List (Lean.Elab.Tactic.TacticM Unit))
    (errMsg : Lean.MessageData) : Lean.Elab.Tactic.TacticM Unit := do
  let rec go : List (Lean.Elab.Tactic.TacticM Unit) → Lean.Elab.Tactic.TacticM Unit
    | [] => throwError errMsg
    | a :: as => do
      let s ← Lean.saveState
      try Lean.Elab.Tactic.withoutRecover a
      catch _ => s.restore; go as
  go acts

private meta def refineHoles (stxM : Lean.Elab.Tactic.TacticM (Lean.TSyntax `term))
    (after : Option (Lean.Elab.Tactic.TacticM (Lean.TSyntax `tactic)) := none) :
    Lean.Elab.Tactic.TacticM Unit := do
  let stx ← stxM
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let (val, mvars) ← Lean.Elab.Tactic.elabTermWithHoles stx (← g.getType) `wram_rand_call true
    let goals ← mvars.filterM fun mv => return (← mv.getKind).isSyntheticOpaque
    g.assign val
    Lean.Elab.Tactic.replaceMainGoal goals
  if let some a := after then Lean.Elab.Tactic.evalTactic (← a)

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_rand_call $h:term) => do
    let tryRfl := some `(tactic| all_goals try rfl)
    let tryOm := some `(tactic| all_goals try omega)
    tryFirstAction
      [ refineHoles `(Cslib.WordRAM.WP.Rand.seq_of_exec $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Rand.of_exec $h ?_) tryRfl,
        refineHoles `(Cslib.WordRAM.WP.Rand.of_execRand $h ?_) tryRfl,
        refineHoles `(Cslib.WordRAM.WP.RandWithin.seq_of_execWithin $h ?_),
        refineHoles `(Cslib.WordRAM.WP.RandWithin.seq_of_exec $h ?_),
        refineHoles `(Cslib.WordRAM.WP.RandWithin.of_execWithin $h ?_ ?_) tryOm,
        refineHoles `(Cslib.WordRAM.WP.RandWithin.of_execRandWithin $h ?_ ?_) tryOm,
        refineHoles `(Cslib.WordRAM.WP.Dist.seq_of_execWithin $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Dist.seq_of_exec $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Dist.of_execWithin $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Dist.of_exec $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Dist.of_execCodeDist $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Dist.of_execRand_le $h ?_ ?_) ]
      m!"wram_rand_call: contract does not apply to the current randomized WP goal"
  | `(tactic| wram_rand_call $h:term with $pats*) => do
    tryFirstAction
      [ refineHoles `(Cslib.WordRAM.WP.Rand.seq_of_exec_spec $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Rand.seq_of_execRand $h ?_ ?_),
        refineHoles `(Cslib.WordRAM.WP.RandWithin.seq_of_execWithin_spec $h ?_),
        refineHoles `(Cslib.WordRAM.WP.RandWithin.seq_of_execRandWithin $h ?_ ?_),
        refineHoles `(Cslib.WordRAM.WP.Dist.seq_of_execWithin_spec $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Dist.seq_of_execCodeDist_const $h ?_ ?_) ]
      m!"wram_rand_call: contract with pattern does not apply to the current randomized WP goal"
    evalTactic (← `(tactic|
      (rintro $pats*
       try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *)))
  | `(tactic| wram_rand_call $h:term renamed $hf:term) => do
    let tryRfl := some `(tactic| all_goals try rfl)
    let tryOm := some `(tactic| all_goals try omega)
    tryFirstAction
      [ refineHoles `(Cslib.WordRAM.WP.Rand.of_execRand_rename $hf $h ?_) tryRfl,
        refineHoles `(Cslib.WordRAM.WP.Rand.seq_of_exec_rename $hf $h ?_),
        refineHoles `(Cslib.WordRAM.WP.Rand.of_exec (Cslib.WordRAM.Exec.rename $hf $h) ?_) tryRfl,
        refineHoles `(Cslib.WordRAM.WP.RandWithin.of_execRandWithin_rename $hf $h ?_ ?_) tryOm,
        refineHoles `(Cslib.WordRAM.WP.Dist.of_execCodeDist
          (Cslib.WordRAM.ExecCodeDist.rename $hf $h) ?_) ]
      m!"wram_rand_call: renamed contract does not apply to the current randomized WP goal"
    evalTactic (← `(tactic|
      try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *))
  | `(tactic| wram_rand_call $h:term renamed $hf:term with $pats*) => do
    tryFirstAction
      [ refineHoles `(Cslib.WordRAM.WP.Rand.seq_of_execRand_rename $hf $h ?_ ?_),
        refineHoles `(Cslib.WordRAM.WP.Rand.seq_of_exec_spec
          (Cslib.WordRAM.Exec.rename_post $hf $h) ?_),
        refineHoles `(Cslib.WordRAM.WP.RandWithin.seq_of_execWithin_spec
          (Cslib.WordRAM.ExecWithin.rename_post $hf $h) ?_),
        refineHoles `(Cslib.WordRAM.WP.Dist.seq_of_execWithin_spec
          (Cslib.WordRAM.ExecWithin.rename_post $hf $h) ?_) ]
      m!"wram_rand_call: renamed contract with pattern does not apply to the current goal"
    evalTactic (← `(tactic|
      (rintro $pats*
       try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *)))

end Cslib.WordRAM

end
