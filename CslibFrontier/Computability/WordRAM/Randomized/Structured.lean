/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import CslibFrontier.Computability.Program.Randomized
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.Randomized.Defs
import CslibFrontier.Tactic.SuppCases

/-!
# Structured randomized word-RAM programs

`Cslib.WordRAM.ExecRand w c x m` is the randomized counterpart of `Cslib.WordRAM.Exec`: at word
size `w`, running the structured program `c : Code B r` from `x : Data r` terminates without
faulting on every path and yields the `ProbComp (Data r × ℕ)` computation `m`, pairing each final
machine data `y` with the exact number of compiled instructions `n` executed along that path.

`Cslib.WordRAM.ExecRandWithin w c x P T R` bundles `ExecRand` with a pathwise postcondition `P`, a
worst-case instruction budget `T`, and a worst-case `rand`-call budget `R` (`IsQueryBounded`),
supporting Hoare-style rules for data instructions, `rand`, sequencing, branches, and potential
loops (`ExecRandWithin.loop_potential`).

WordRAM instantiates the exact randomized assembly theorem of `Cslib.Program.ExecRand` with
its bounded uniform draw. Every structured randomized execution refines `Code.assemble`
(`ExecRand.runRand_assemble`). Compiling with `Code.program out` establishes `RandHaltsWithin`,
`RandCallsBounded`, and the memory postcondition `P` directly on `RandCfg.halted`
(`ExecRandWithin.program`).

## Main definitions

* `Cslib.WordRAM.ExecRand`: exact randomized execution of `Code B r` into `ProbComp (Data r × ℕ)`.
* `Cslib.WordRAM.codeComp`: canonical `ProbComp (Data r × ℕ)` associated with `(w, c, x)`.
* `Cslib.WordRAM.ExecRandWithin`: pathwise postcondition, worst-case instruction bound, and
  `rand`-call budget on `Code B r`.

## Main results

* `Cslib.WordRAM.ExecRand.unique`: `m` is uniquely determined by `(w, c, x)`.
* `Cslib.WordRAM.Exec.execRand`, `Cslib.WordRAM.ExecWithin.execRandWithin`: deterministic
  structured executions lift with zero `rand` calls.
* `Cslib.WordRAM.ExecRandWithin.loop_potential`: potential-based termination, worst-case time, and
  `rand`-call rule for randomized loops.
* `Cslib.WordRAM.ExecRand.runRand_assemble`, `Cslib.WordRAM.ExecRand.runRand_program`,
  `Cslib.WordRAM.Exec.runRand_program`, `Cslib.WordRAM.ExecRandWithin.program`: assembly
  refinement into flat `runRand`, `RandHaltsWithin`, and `RandCallsBounded`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r r' : ℕ}

/-! ## Structured randomized executions -/

/-- `ExecRand w c x m`: at word size `w`, the structured program `c` runs from data `x` without
faulting on any path and induces the `ProbComp (Data r × ℕ)` computation `m` of `(finalData, steps)`
matching the exact instruction counts of `Code.assemble`. -/
inductive ExecRand (w : ℕ) : Code B r → Data r → ProbComp (Data r × ℕ) → Prop where
  /-- A data instruction executes in `1` instruction and issues `0` calls. -/
  | op {o : Op B r} {x y : Data r} (h : o.eval w x = some y) :
      ExecRand w (.op o) x (pure (y, 1))
  /-- `Code.rand dst src` draws uniformly from `[0, x.regs src]` in `1` instruction when the bound
  fits a word. -/
  | rand {dst src : Fin r} {x : Data r} (h : Fits w (x.regs src)) :
      ExecRand w (.rand dst src) x (do
        let k ← ProbComp.unifFin (x.regs src)
        pure (x.set dst k.val, 1))
  /-- Sequencing composes the two computations and adds their instruction counts. -/
  | seq {c₁ c₂ : Code B r} {x : Data r} {m₁ : ProbComp (Data r × ℕ)}
      {m₂ : Data r → ProbComp (Data r × ℕ)}
      (h₁ : ExecRand w c₁ x m₁)
      (h₂ : ∀ z ∈ m₁.support, ExecRand w c₂ z.1 (m₂ z.1)) :
      ExecRand w (.seq c₁ c₂) x (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2))
  /-- Taking the positive branch adds `1` instruction for the branch test. -/
  | branch_pos {c : Cond r} {pos neg : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
      (hc : c.Holds x) (h : ExecRand w pos x m) :
      ExecRand w (.branch c pos neg) x ((fun z => (z.1, z.2 + 1)) <$> m)
  /-- Taking the negative branch adds `2` instructions (branch test and jump past `pos`). -/
  | branch_neg {c : Cond r} {pos neg : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
      (hc : ¬c.Holds x) (h : ExecRand w neg x m) :
      ExecRand w (.branch c pos neg) x ((fun z => (z.1, z.2 + 2)) <$> m)
  /-- Exiting a loop when the condition fails takes `2` instructions (branch test and exit jump). -/
  | loop_exit {c : Cond r} {body : Code B r} {x : Data r} (hc : ¬c.Holds x) :
      ExecRand w (.loop c body) x (pure (x, 2))
  /-- Entering a loop executes `body`, jumps back to the header, and continues the loop, adding `2`
  instructions for the branch test and back-jump. -/
  | loop_iter {c : Cond r} {body : Code B r} {x : Data r} {mb : ProbComp (Data r × ℕ)}
      {ml : Data r → ProbComp (Data r × ℕ)}
      (hc : c.Holds x)
      (hb : ExecRand w body x mb)
      (hl : ∀ z ∈ mb.support, ExecRand w (.loop c body) z.1 (ml z.1)) :
      ExecRand w (.loop c body) x (do
        let z₁ ← mb
        let z₂ ← ml z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + 2))

namespace ExecRand

variable {w : ℕ}

/-- The `ProbComp` tree of a structured execution is uniquely determined by `(w, c, x)`. -/
theorem unique {c : Code B r} {x : Data r} {m m' : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) (h' : ExecRand w c x m') : m = m' := by
  induction h generalizing m' with
  | op ho => cases h' with | op ho' => rw [ho] at ho'; cases ho'; rfl
  | rand _ => cases h'; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h' with
    | seq h₁' h₂' =>
      obtain rfl := ih₁ h₁'
      exact OracleComp.bind_congr_on_support fun z₁ hz₁ => by rw [ih₂ z₁ hz₁ (h₂' z₁ hz₁)]
  | branch_pos _ _ ih | branch_neg _ _ ih => cases h' <;> first | contradiction | rw [ih ‹_›]
  | loop_exit _ => cases h' <;> first | rfl | contradiction
  | loop_iter _ _ _ ihb ihl =>
    cases h' with
    | loop_exit => contradiction
    | loop_iter _ hb' hl' =>
      obtain rfl := ihb hb'
      exact OracleComp.bind_congr_on_support fun z₁ hz₁ => by rw [ihl z₁ hz₁ (hl' z₁ hz₁)]

/-- Every structured execution takes at least `1` instruction on every path. -/
theorem pos {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) {z : Data r × ℕ} (hz : z ∈ m.support) : 1 ≤ z.2 := by
  induction h generalizing z with
  | op _ | rand _ | branch_pos _ _ _ | branch_neg _ _ _ | loop_exit _ | loop_iter _ _ _ _ _ =>
    supp_cases hz
    omega
  | seq _ _ ih₁ _ =>
    supp_cases hz with ⟨z₁, hz₁, z₂, -, rfl⟩
    have := ih₁ hz₁
    omega

/-- Structured randomized executions preserve word-boundedness on every supported path. -/
theorem bounded {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) (hx : x.Bounded w) {z : Data r × ℕ} (hz : z ∈ m.support) :
    z.1.Bounded w := by
  induction h generalizing z with
  | op ho =>
    supp_cases hz
    exact hx.op ho
  | rand hfit =>
    supp_cases hz with ⟨k, rfl⟩
    exact hx.set (hfit.of_le (Nat.le_of_lt_succ k.isLt))
  | seq _ _ ih₁ ih₂ | loop_iter _ _ _ ih₁ ih₂ =>
    supp_cases hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    exact (ih₂ z₁ hz₁ (ih₁ hx hz₁) hz₂ :)
  | branch_pos _ _ ih | branch_neg _ _ ih =>
    supp_cases hz with ⟨z₀, hz₀, rfl⟩
    exact (ih hx hz₀ :)
  | loop_exit _ =>
    supp_cases hz
    exact hx

/-- A register that `c` does not write retains its value on every supported path. -/
theorem regs_eq {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)} {i : Fin r}
    (h : ExecRand w c x m) (hi : c.Preserves i) {z : Data r × ℕ} (hz : z ∈ m.support) :
    z.1.regs i = x.regs i := by
  induction h generalizing z with
  | op ho =>
    supp_cases hz
    exact (Exec.op ho).regs_eq hi
  | rand _ =>
    supp_cases hz
    simp only [Data.set_regs, Function.update_of_ne (Ne.symm hi)]
  | seq _ _ ih₁ ih₂ =>
    supp_cases hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    exact (ih₂ z₁ hz₁ hi.2 hz₂ :).trans (ih₁ hi.1 hz₁)
  | branch_pos _ _ ih =>
    supp_cases hz with ⟨z₀, hz₀, rfl⟩
    exact (ih hi.1 hz₀ :)
  | branch_neg _ _ ih =>
    supp_cases hz with ⟨z₀, hz₀, rfl⟩
    exact (ih hi.2 hz₀ :)
  | loop_exit _ =>
    supp_cases hz
    rfl
  | loop_iter _ _ _ ihb ihl =>
    supp_cases hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    exact (ihl z₁ hz₁ hi hz₂ :).trans (ihb hi hz₁)

end ExecRand

/-- Canonical `ProbComp (Data r × ℕ)` of a structured program `c` from `x` when `ExecRand w c x m`
holds for some `m` (unique by `ExecRand.unique`), and `pure (x, 0)` otherwise. -/
noncomputable def codeComp (w : ℕ) (c : Code B r) (x : Data r) : ProbComp (Data r × ℕ) :=
  open Classical in
  if h : ∃ m, ExecRand w c x m then h.choose else pure (x, 0)

/-- When `ExecRand w c x m` holds, `codeComp w c x` equals `m`. -/
theorem ExecRand.codeComp_eq {w : ℕ} {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) : codeComp w c x = m := by
  classical
  have hex : ∃ m', ExecRand w c x m' := ⟨m, h⟩
  simp only [codeComp, hex, ↓reduceDIte]
  exact hex.choose_spec.unique h

/-- Every deterministic structured execution `Exec w c x y n` lifts to
`ExecRand w c x (pure (y, n))`. -/
theorem Exec.execRand {w : ℕ} {c : Code B r} {x y : Data r} {n : ℕ} (h : Exec w c x y n) :
    ExecRand w c x (pure (y, n)) := by
  induction h with
  | op ho => exact .op ho
  | @seq c₁ c₂ x y z m n _ _ ih₁ ih₂ =>
    have hseq := ExecRand.seq ih₁ (m₂ := fun _ => pure (z, n)) fun z' hz' => by
      cases OracleComp.eq_of_mem_supportWith_pure hz'
      exact ih₂
    simpa only [pure_bind] using hseq
  | branch_pos hc _ ih =>
    simpa only [map_pure] using ExecRand.branch_pos hc ih
  | branch_neg hc _ ih =>
    simpa only [map_pure] using ExecRand.branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | @loop_iter c body x y z m n hc _ _ ihb ihl =>
    have hiter := ExecRand.loop_iter hc ihb (ml := fun _ => pure (z, n)) fun z' hz' => by
      cases OracleComp.eq_of_mem_supportWith_pure hz'
      exact ihl
    simpa only [pure_bind] using hiter

/-- Prepending a deterministic `Exec` onto a randomized `ExecRand` shifts the instruction count by
`n₁`. -/
theorem Exec.seqRand {w : ℕ} {c₁ c₂ : Code B r} {x y : Data r} {n₁ : ℕ}
    {m₂ : ProbComp (Data r × ℕ)} (h₁ : Exec w c₁ x y n₁) (h₂ : ExecRand w c₂ y m₂) :
    ExecRand w (.seq c₁ c₂) x ((fun z => (z.1, n₁ + z.2)) <$> m₂) := by
  have hseq := ExecRand.seq h₁.execRand (m₂ := fun _ => m₂) fun z' hz' => by
    cases OracleComp.eq_of_mem_supportWith_pure hz'
    exact h₂
  simpa only [pure_bind, ← bind_pure_comp] using hseq

/-! ## Renaming registers in structured randomized executions -/

section Rename

variable {f : Fin r → Fin r'}

private theorem ExecRand.rename_bind_step (hf : f.Injective) {w extra : ℕ} {c₂ : Code B r}
    (x : Data r') {m₁ : ProbComp (Data r × ℕ)} {m₂ : Data r → ProbComp (Data r × ℕ)}
    (h₂ : ∀ z ∈ m₁.support, ExecRand w c₂ z.1 (m₂ z.1))
    (ih₂ : ∀ z₁ ∈ m₁.support, ∀ {x' : Data r'}, x'.comap f = z₁.1 →
      ExecRand w (c₂.rename f) x' ((fun z => (z.1.extend f x', z.2)) <$> m₂ z₁.1)) :
    ∃ m₂' : Data r' → ProbComp (Data r' × ℕ),
      (∀ z' ∈ ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> m₁).support,
        ExecRand w (c₂.rename f) z'.1 (m₂' z'.1)) ∧
      ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + extra))) = (do
        let z₁ ← (fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> m₁
        let z₂ ← m₂' z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + extra)) := by
  refine ⟨fun d => (fun z => (z.1.extend f x, z.2)) <$> codeComp w c₂ (d.comap f),
    fun z' hz' => ?_, ?_⟩
  · supp_cases hz' with ⟨z₁, hz₁, rfl⟩
    dsimp only
    rw [Data.comap_extend hf, (h₂ z₁ hz₁).codeComp_eq]
    simpa only [Data.extend_extend hf] using ih₂ z₁ hz₁ (Data.comap_extend hf z₁.1 x)
  · simp only [← bind_pure_comp, bind_assoc, pure_bind]
    refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
    rw [Data.comap_extend hf, (h₂ z₁ hz₁).codeComp_eq]

/-- Running a structured randomized program through an injective register map `f` transforms its
outputs via `Data.extend f x`, preserving instruction counts and untouched registers. -/
theorem ExecRand.rename (hf : f.Injective) {w : ℕ} {c : Code B r} {x : Data r'}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c (x.comap f) m) :
    ExecRand w (c.rename f) x ((fun z => (z.1.extend f x, z.2)) <$> m) := by
  generalize hx : x.comap f = x₀ at h
  induction h generalizing x with
  | @op o _ y ho =>
    subst hx
    have ho' : (o.rename f).eval w x = some (y.extend f x) := by rw [Op.eval_rename hf, ho]; rfl
    simpa only [Code.rename, map_pure] using ExecRand.op ho'
  | @rand dst src _ hfit =>
    subst hx
    have heq : ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> (do
        let k ← ProbComp.unifFin (x.regs (f src))
        pure ((x.comap f).set dst k.val, 1))) = (do
        let k ← ProbComp.unifFin (x.regs (f src))
        pure (x.set (f dst) k.val, 1)) := by
      rw [← bind_pure_comp, bind_assoc]
      refine congrArg (ProbComp.unifFin (x.regs (f src)) >>= ·) (funext fun k => ?_)
      simp only [pure_bind, Data.extend_set hf, Data.extend_comap hf]
    simpa only [Code.rename, Data.comap_regs, heq] using ExecRand.rand (x := x) hfit
  | @seq c₁ c₂ _ m₁ m₂ _ h₂ ih₁ ih₂ =>
    subst hx
    obtain ⟨_, hcont, heq⟩ := rename_bind_step (extra := 0) hf x h₂ fun z₁ hz₁ {_} h => ih₂ z₁ hz₁ h
    simp only [Nat.add_zero] at heq
    simpa only [Code.rename, ← heq] using ExecRand.seq (ih₁ rfl) hcont
  | @branch_pos cond pos neg _ m hc _ ih =>
    subst hx
    simpa only [Code.rename, Functor.map_map] using
      ExecRand.branch_pos (neg := neg.rename f) ((Cond.holds_rename _ _).2 hc) (ih rfl)
  | @branch_neg cond pos neg _ m hc _ ih =>
    subst hx
    simpa only [Code.rename, Functor.map_map] using
      ExecRand.branch_neg (pos := pos.rename f) (fun h => hc ((Cond.holds_rename _ _).1 h)) (ih rfl)
  | @loop_exit cond body _ hc =>
    subst hx
    simpa only [Code.rename, map_pure, Data.extend_comap hf] using
      ExecRand.loop_exit (body := body.rename f) (fun h => hc ((Cond.holds_rename _ _).1 h))
  | @loop_iter cond body _ mb ml hc _ hl ihb ihl =>
    subst hx
    obtain ⟨_, hcont, heq⟩ := rename_bind_step (extra := 2) hf x hl fun z₁ hz₁ {_} h => ihl z₁ hz₁ h
    simp only [Code.rename] at hcont ⊢
    simpa only [← heq] using ExecRand.loop_iter ((Cond.holds_rename _ _).2 hc) (ihb rfl) hcont

end Rename

/-! ## Hoare-style bounded structured execution (`ExecRandWithin`) -/

/-- `ExecRandWithin w c x P T R`: at word size `w`, running `c` from `x` terminates cleanly on every
path (`ExecRand`), makes at most `R` `rand` calls on every path, and every supported outcome
`(y, n)` satisfies `P y` and `n ≤ T`. -/
def ExecRandWithin (w : ℕ) (c : Code B r) (x : Data r) (P : Data r → Prop) (T R : ℕ) : Prop :=
  ∃ m, ExecRand w c x m ∧ m.IsQueryBounded R ∧ ∀ z ∈ m.support, P z.1 ∧ z.2 ≤ T

/-- Every deterministic `ExecWithin` lifts to `ExecRandWithin` with `0` `rand` calls. -/
theorem ExecWithin.execRandWithin {w T : ℕ} {c : Code B r} {x y : Data r} {P : Data r → Prop}
    (h : ExecWithin w c x y T) (hy : P y) :
    ExecRandWithin w c x P T 0 := by
  obtain ⟨n, hn, he⟩ := h
  refine ⟨pure (y, n), he.execRand, .pure _ 0, fun z hz => ?_⟩
  cases OracleComp.eq_of_mem_supportWith_pure hz
  exact ⟨hy, hn⟩

namespace ExecRandWithin

variable {w : ℕ} {c c₁ c₂ pos neg body : Code B r} {cond : Cond r} {x : Data r}
  {P Q : Data r → Prop} {T T' T₁ T₂ R R' R₁ R₂ : ℕ}

/-- Monotonicity / consequence rule for `ExecRandWithin`. -/
theorem mono (h : ExecRandWithin w c x P T R) (hPQ : ∀ y, P y → Q y)
    (hT : T ≤ T') (hR : R ≤ R') :
    ExecRandWithin w c x Q T' R' := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  exact ⟨m, hm, hq.mono hR, fun z hz => ⟨hPQ z.1 (hsup z hz).1, (hsup z hz).2.trans hT⟩⟩

/-- Strengthening `P` with `Data.Bounded w` when `x.Bounded w` holds initially. -/
theorem withBounded (h : ExecRandWithin w c x P T R) (hx : x.Bounded w) :
    ExecRandWithin w c x (fun y => P y ∧ y.Bounded w) T R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  exact ⟨m, hm, hq, fun z hz => ⟨⟨(hsup z hz).1, hm.bounded hx hz⟩, (hsup z hz).2⟩⟩

/-- Strengthening `P` with preservation of a register `i` not written by `c`. -/
theorem withPreserves {i : Fin r} (h : ExecRandWithin w c x P T R) (hi : c.Preserves i) :
    ExecRandWithin w c x (fun y => P y ∧ y.regs i = x.regs i) T R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  exact ⟨m, hm, hq, fun z hz => ⟨⟨(hsup z hz).1, hm.regs_eq hi hz⟩, (hsup z hz).2⟩⟩

/-- A single `op` instruction runs in `1` step and `0` `rand` calls. -/
theorem op {o : Op B r} {y : Data r} (ho : o.eval w x = some y) (hy : P y) :
    ExecRandWithin w (.op o) x P 1 0 :=
  (ExecWithin.op ho).execRandWithin hy

/-- `Code.rand dst src` runs in `1` step and `1` `rand` call when `x.regs src` fits a word. -/
theorem rand {dst src : Fin r} (hfit : Fits w (x.regs src))
    (hk : ∀ k : Fin (x.regs src + 1), P (x.set dst k.val)) :
    ExecRandWithin (B := B) w (.rand dst src) x P 1 1 := by
  refine ⟨_, ExecRand.rand hfit, ?_, ?_⟩
  · simpa only [Nat.add_zero] using
      (ProbComp.isQueryBounded_unifFin (x.regs src)).bind fun _ => .pure _ 0
  · intro z hz
    supp_cases hz with ⟨k, rfl⟩
    exact ⟨hk k, le_rfl⟩

/-- Sequencing rule: composes `ExecRandWithin` specs and sums both step and call budgets. -/
theorem seq (h₁ : ExecRandWithin w c₁ x P T₁ R₁)
    (h₂ : ∀ y, P y → ExecRandWithin w c₂ y Q T₂ R₂) :
    ExecRandWithin w (.seq c₁ c₂) x Q (T₁ + T₂) (R₁ + R₂) := by
  obtain ⟨m₁, hm₁, hq₁, hsup₁⟩ := h₁
  have hstep : ∀ z₁ ∈ m₁.support,
      ExecRand w c₂ z₁.1 (codeComp w c₂ z₁.1) ∧
      (codeComp w c₂ z₁.1).IsQueryBounded R₂ ∧
      ∀ z₂ ∈ (codeComp w c₂ z₁.1).support, Q z₂.1 ∧ z₂.2 ≤ T₂ := by
    intro z₁ hz₁
    obtain ⟨m₂, hm₂, hq₂, hsup₂⟩ := h₂ z₁.1 (hsup₁ z₁ hz₁).1
    rw [hm₂.codeComp_eq]
    exact ⟨hm₂, hq₂, hsup₂⟩
  refine ⟨_, ExecRand.seq hm₁ fun z₁ hz₁ => (hstep z₁ hz₁).1, ?_, ?_⟩
  · refine OracleComp.IsCostBounded.bind_on_support hq₁ fun z₁ hz₁ => ?_
    simpa only [Nat.add_zero] using
      (hstep z₁ hz₁).2.1.bind fun _ => .pure _ 0
  · intro z hz
    supp_cases hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    exact ⟨((hstep z₁ hz₁).2.2 z₂ hz₂).1,
      Nat.add_le_add (hsup₁ z₁ hz₁).2 ((hstep z₁ hz₁).2.2 z₂ hz₂).2⟩

/-- Positive branch rule (`+1` step, same call budget). -/
theorem branch_pos (hc : cond.Holds x) (h : ExecRandWithin w pos x P T R) :
    ExecRandWithin w (.branch cond pos neg) x P (T + 1) R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  refine ⟨_, ExecRand.branch_pos hc hm, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_⟩
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  exact ⟨(hsup z₀ hz₀).1, Nat.add_le_add_right (hsup z₀ hz₀).2 1⟩

/-- Negative branch rule (`+2` steps, same call budget). -/
theorem branch_neg (hc : ¬cond.Holds x) (h : ExecRandWithin w neg x P T R) :
    ExecRandWithin w (.branch cond pos neg) x P (T + 2) R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  refine ⟨_, ExecRand.branch_neg hc hm, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_⟩
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  exact ⟨(hsup z₀ hz₀).1, Nat.add_le_add_right (hsup z₀ hz₀).2 2⟩

/-- Combined branch rule with common budgets `(T + 2, R)`. -/
theorem branch (hpos : cond.Holds x → ExecRandWithin w pos x P T R)
    (hneg : ¬cond.Holds x → ExecRandWithin w neg x P T R) :
    ExecRandWithin w (.branch cond pos neg) x P (T + 2) R := by
  by_cases hc : cond.Holds x
  · exact (branch_pos hc (hpos hc)).mono (fun _ h => h) (by omega) le_rfl
  · exact branch_neg hc (hneg hc)

/-- Exiting a loop when the condition fails takes `2` steps and `0` `rand` calls. -/
theorem loop_exit (hc : ¬cond.Holds x) (hx : P x) :
    ExecRandWithin w (.loop cond body) x P 2 0 :=
  (ExecWithin.loop_exit hc).execRandWithin hx

/-- One iteration of a loop followed by the rest adds `T₁ + 2` steps and `R₁ + R₂` calls. -/
theorem loop_iter (hc : cond.Holds x)
    (hb : ExecRandWithin w body x P T₁ R₁)
    (hl : ∀ y, P y → ExecRandWithin w (.loop cond body) y Q T₂ R₂) :
    ExecRandWithin w (.loop cond body) x Q (T₁ + T₂ + 2) (R₁ + R₂) := by
  obtain ⟨mb, hmb, hqb, hsupb⟩ := hb
  have hstep : ∀ z₁ ∈ mb.support,
      ExecRand w (.loop cond body) z₁.1 (codeComp w (.loop cond body) z₁.1) ∧
      (codeComp w (.loop cond body) z₁.1).IsQueryBounded R₂ ∧
      ∀ z₂ ∈ (codeComp w (.loop cond body) z₁.1).support, Q z₂.1 ∧ z₂.2 ≤ T₂ := by
    intro z₁ hz₁
    obtain ⟨ml, hml, hql, hsupl⟩ := hl z₁.1 (hsupb z₁ hz₁).1
    rw [hml.codeComp_eq]
    exact ⟨hml, hql, hsupl⟩
  refine ⟨_, ExecRand.loop_iter hc hmb fun z₁ hz₁ => (hstep z₁ hz₁).1, ?_, ?_⟩
  · refine OracleComp.IsCostBounded.bind_on_support hqb fun z₁ hz₁ => ?_
    simpa only [Nat.add_zero] using
      (hstep z₁ hz₁).2.1.bind fun _ => .pure _ 0
  · intro z hz
    supp_cases hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    exact ⟨((hstep z₁ hz₁).2.2 z₂ hz₂).1,
      Nat.add_le_add_right (Nat.add_le_add (hsupb z₁ hz₁).2 ((hstep z₁ hz₁).2.2 z₂ hz₂).2) 2⟩

/-- **Potential rule for randomized loops.** Suppose every state `x` satisfying `I x` and
`cond.Holds x` runs `body` within some `T_b` instructions and `R_b` `rand` calls such that every
supported successor `y` satisfies `I y`, `T_b + 2 + Φ y ≤ Φ x`, and `R_b + Ψ y ≤ Ψ x`. Then from
any `x` satisfying `I x`, `.loop cond body` terminates within `Φ x + 2` instructions and `Ψ x`
`rand` calls, reaching a state `y` with `I y ∧ ¬cond.Holds y`. -/
theorem loop_potential (I : Data r → Prop) (Φ Ψ : Data r → ℕ)
    (hbody : ∀ x, I x → cond.Holds x → ∃ T_b R_b,
      ExecRandWithin w body x
        (fun y => I y ∧ T_b + 2 + Φ y ≤ Φ x ∧ R_b + Ψ y ≤ Ψ x) T_b R_b)
    (hx : I x) :
    ExecRandWithin w (.loop cond body) x (fun y => I y ∧ ¬cond.Holds y) (Φ x + 2) (Ψ x) := by
  induction hm : Φ x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    subst hm
    by_cases hc : cond.Holds x
    · obtain ⟨T_b, R_b, hb⟩ := hbody x hx hc
      obtain ⟨mb, -, -, hsupb⟩ := id hb
      obtain ⟨z₀, hz₀⟩ := ProbComp.support_nonempty mb
      obtain ⟨-, hΦ₀, hΨ₀⟩ := (hsupb z₀ hz₀).1
      have hstep : ExecRandWithin w (.loop cond body) x (fun y => I y ∧ ¬cond.Holds y)
          (T_b + (Φ x - T_b - 2 + 2) + 2) (R_b + (Ψ x - R_b)) := by
        refine loop_iter hc hb ?_
        rintro y ⟨hIy, hΦy, hΨy⟩
        exact (ih (Φ y) (by omega) hIy rfl).mono (fun _ h => h) (by omega) (by omega)
      exact hstep.mono (fun _ h => h) (by omega) (by omega)
    · exact (loop_exit hc ⟨hx, hc⟩).mono (fun _ h => h) (by omega) (Nat.zero_le _)

/-- Renaming a `ExecRandWithin` specification along an injective register map `f`. -/
theorem rename {f : Fin r → Fin r'} (hf : f.Injective) {x : Data r'}
    (h : ExecRandWithin w c (x.comap f) P T R) :
    ExecRandWithin w (c.rename f) x (fun y' => ∃ y, P y ∧ y' = y.extend f x) T R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  refine ⟨_, hm.rename hf, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_⟩
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  exact ⟨⟨z₀.1, (hsup z₀ hz₀).1, rfl⟩, (hsup z₀ hz₀).2⟩

end ExecRandWithin

/-! ## Compilation to flat `runRand`, `RandHaltsWithin`, and `RandCallsBounded` -/

section Compile

variable {w : ℕ} {p : Program B r}

private def evalGenericOp (w : ℕ) : GenericOp B r → Data r → Option (ProbComp (Data r))
  | .inl op, x => (op.eval w x).map pure
  | .inr (dst, src), x =>
    if Fits w (x.regs src) then
      some ((fun k => x.set dst k.val) <$> ProbComp.unifFin (x.regs src))
    else none

private abbrev randomizedFlatMachine (w : ℕ) (B : Basis) (r : ℕ) :
    Cslib.Program.RandomizedFlatMachine (evalGenericOp w) (flatMachine w B r) where
  Config := RandCfg r
  running pc x := .running ⟨pc, x⟩
  step := stepRand w
  step_op := by
    intro p pc op x m hp h
    cases op with
    | inl op =>
      cases he : op.eval w x with
      | none => simp [evalGenericOp, he] at h
      | some y =>
        simp only [evalGenericOp, he, Option.map_some, Option.some.injEq] at h
        subst m
        simpa using stepRand_op (s := ⟨pc, x⟩) hp he
    | inr regs =>
      obtain ⟨dst, src⟩ := regs
      by_cases hfit : Fits w (x.regs src)
      · simp only [evalGenericOp, hfit, ↓reduceIte, Option.some.injEq] at h
        subst m
        rw [stepRand_rand_of_fits (s := ⟨pc, x⟩) hp hfit, Functor.map_map]
        rfl
      · simp [evalGenericOp, hfit] at h
  step_goto hp := stepRand_jump hp
  step_jumpIf_pos := by
    intro p pc target cond x hp h
    change cond.Holds x at h
    simpa only [h, ↓reduceIte] using stepRand_branch (w := w) (s := ⟨pc, x⟩) hp
  step_jumpIf_neg := by
    intro p pc target cond x hp h
    change ¬cond.Holds x at h
    simpa only [h, ↓reduceIte] using stepRand_branch (w := w) (s := ⟨pc, x⟩) hp

private theorem run_generic (p : Program B r) (T : ℕ) (cfg : RandCfg r) :
    (randomizedFlatMachine w B r).run p T cfg = runRand w p T cfg := by
  induction T generalizing cfg with
  | zero => rw [Cslib.Program.RandomizedFlatMachine.run_zero, runRand_zero]
  | succ T ih =>
    rw [Cslib.Program.RandomizedFlatMachine.run_succ, runRand_succ]
    exact congrArg (stepRand w p cfg >>= ·) (funext ih)

private theorem ExecRand.toGeneric {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) :
    Cslib.Program.ExecRand (I := instructionSet w B r) (evalGenericOp w) c.toGeneric x m := by
  induction h with
  | @op o x y h =>
    simpa [Code.toGeneric] using Cslib.Program.ExecRand.op (I := instructionSet w B r)
      (evalRand := evalGenericOp w) (o := .inl o) (x := x) (m := pure y)
      (by simp [evalGenericOp, h])
  | @rand dst src x h =>
    simpa only [Code.toGeneric, ← bind_pure_comp, bind_assoc, pure_bind] using
      Cslib.Program.ExecRand.op (I := instructionSet w B r)
        (evalRand := evalGenericOp w) (o := .inr (dst, src)) (x := x)
        (m := (fun k => x.set dst k.val) <$> ProbComp.unifFin (x.regs src))
        (by simp [evalGenericOp, h])
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos h _ ih => exact .branch_pos h ih
  | branch_neg h _ ih => exact .branch_neg h ih
  | loop_exit h => exact .loop_exit h
  | loop_iter h _ _ ihb ihl => exact .loop_iter h ihb ihl

/-- **Randomized assembly is exact.** Running a flat program `p` containing `c.assemble pc` at `pc`
for `T` steps (where every path of `m` uses at most `T` steps) is equal in `ProbComp` to sampling
`(y, n) ← m` and continuing from `⟨pc + c.size, y⟩` for the remaining `T - n` steps. -/
theorem ExecRand.runRand_assemble {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    {pc T : ℕ} (h : ExecRand w c x m) (hp : p.Contains pc (c.assemble pc))
    (hT : ∀ z ∈ m.support, z.2 ≤ T) :
    runRand w p T (.running ⟨pc, x⟩) = (do
      let z ← m
      runRand w p (T - z.2) (.running ⟨pc + c.size, z.1⟩)) := by
  have hp' : Cslib.Program.Contains p pc (c.toGeneric.assemble (flatMachine w B r) pc) := by
    rw [Code.assemble_toGeneric]
    exact hp
  simpa only [run_generic, Code.size_toGeneric] using
    h.toGeneric.runRand_assemble (randomizedFlatMachine w B r) hp' hT

/-- Compiling `c` with `Code.program out` maps every `(y, n)` of `m` to `.halted (y.regs out) y`
once `T ≥ n + 1` on every path. -/
theorem ExecRand.runRand_program {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) (out : Fin r) {T : ℕ} (hT : ∀ z ∈ m.support, z.2 + 1 ≤ T) :
    runRand w (c.program out) T (.running ⟨0, x⟩) =
      (fun z => RandCfg.halted (z.1.regs out) z.1) <$> m := by
  have hT_le : ∀ z ∈ m.support, z.2 ≤ T := fun z hz => Nat.le_of_succ_le (hT z hz)
  rw [h.runRand_assemble (Program.Contains.self (c.program out)).append_left hT_le,
    ← bind_pure_comp]
  refine OracleComp.bind_congr_on_support fun z hz => ?_
  have h1 := hT z hz
  obtain ⟨k, hk⟩ : ∃ k, T - z.2 = k + 1 := ⟨T - z.2 - 1, by omega⟩
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by
    simp [Code.program]
  rw [hk, runRand_succ, stepRand_halt (s := ⟨0 + c.size, z.1⟩) hhalt, pure_bind, runRand_halted]

/-- Structured deterministic corollary: a compiled `Exec w c x y n` halts cleanly under `runRand`
with output `y.regs out` and final machine data `y` at any fuel `T ≥ n + 1`. -/
theorem Exec.runRand_program {c : Code B r} {x y : Data r} {n T : ℕ}
    (h : Exec w c x y n) (out : Fin r) (hT : n + 1 ≤ T) :
    runRand w (c.program out) T (.running ⟨0, x⟩) = pure (.halted (y.regs out) y) := by
  rw [h.execRand.runRand_program out fun z hz => by
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact hT]
  rfl

/-- Compiling an `ExecRandWithin w c x P T R` certificate via `c.program out` yields
`RandHaltsWithin`, `RandCallsBounded`, and pathwise `P` on the halting data at any fuel
`T' ≥ T + 1`. -/
theorem ExecRandWithin.program {c : Code B r} {x : Data r} {P : Data r → Prop} {T T' R : ℕ}
    (h : ExecRandWithin w c x P T R) (out : Fin r) (hT : T + 1 ≤ T') :
    RandHaltsWithin w (c.program out) ⟨0, x⟩ T' ∧
    RandCallsBounded w (c.program out) ⟨0, x⟩ T' R ∧
    ∀ cfg ∈ (runRand w (c.program out) T' (.running ⟨0, x⟩)).support,
      ∃ y, cfg = .halted (y.regs out) y ∧ P y := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  have hrun := hm.runRand_program out (T := T') fun z hz =>
    (Nat.add_le_add_right (hsup z hz).2 1).trans hT
  refine ⟨?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs out, z.1, rfl⟩
  · rw [RandCallsBounded, hrun]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr hq
  · intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, hz, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1, rfl, (hsup z hz).1⟩

end Compile

end Cslib.WordRAM

end
