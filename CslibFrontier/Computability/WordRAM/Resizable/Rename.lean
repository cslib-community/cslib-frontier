/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Resizable.Basic

/-!
# Register Renaming for Structured Resizable Word RAM Programs (`RCode.rename`)

Provides register-view projection (`RData.comap`), write-back extension (`RData.extend`), structured
program renaming (`RCode.rename`), and big-step demonic execution lifting (`RDemonicExec.rename`,
`RDemonicExec.rename_eq`) along injective register maps `f : Fin r → Fin r'`, mirroring
`Cslib.WordRAM.Code.rename` and `Cslib.WordRAM.Exec.rename` on `Cslib.WordRAM.Resizable`.

## Main definitions

* `Cslib.WordRAM.Resizable.RData.comap`, `Cslib.WordRAM.Resizable.RData.extend`: register-view
  projection and write-back extension on `RData`.
* `Cslib.WordRAM.Resizable.RCode.rename`: register renaming on `RCode B r`.

## Main results

* `Cslib.WordRAM.Resizable.RCode.readsWidth_rename`: register renaming preserves `ReadsWidth`.
* `Cslib.WordRAM.Resizable.RDemonicExec.rename`, `Cslib.WordRAM.Resizable.RDemonicExec.rename_eq`:
  lifting `RDemonicExec` along injective register embeddings while preserving unmapped registers.
-/

@[expose] public section

namespace Cslib.WordRAM.Resizable

open Cslib.WordRAM

variable {B : Basis} {r r' : ℕ}

namespace RData

/-- View `x : RData r'` on `r` registers along `f : Fin r → Fin r'`. -/
def comap (f : Fin r → Fin r') (x : RData r') : RData r :=
  ⟨x.regs ∘ f, x.mem, x.frontier⟩

/-- Write the registers, memory, and frontier of `y : RData r` back into `x : RData r'` along `f`,
preserving registers outside `Set.range f`. -/
noncomputable def extend (f : Fin r → Fin r') (y : RData r) (x : RData r') : RData r' :=
  ⟨(y.toData.extend f x.toData).regs, y.mem, y.frontier⟩

@[simp] theorem toData_comap (f : Fin r → Fin r') (x : RData r') :
    (x.comap f).toData = x.toData.comap f := rfl

@[simp] theorem comap_regs (f : Fin r → Fin r') (x : RData r') (i : Fin r) :
    (x.comap f).regs i = x.regs (f i) := rfl

@[simp] theorem comap_mem (f : Fin r → Fin r') (x : RData r') :
    (x.comap f).mem = x.mem := rfl

@[simp] theorem comap_frontier (f : Fin r → Fin r') (x : RData r') :
    (x.comap f).frontier = x.frontier := rfl

@[simp] theorem toData_extend (f : Fin r → Fin r') (y : RData r) (x : RData r') :
    (y.extend f x).toData = y.toData.extend f x.toData := rfl

@[simp] theorem extend_mem (f : Fin r → Fin r') (y : RData r) (x : RData r') :
    (y.extend f x).mem = y.mem := rfl

@[simp] theorem extend_frontier (f : Fin r → Fin r') (y : RData r) (x : RData r') :
    (y.extend f x).frontier = y.frontier := rfl

theorem comap_extend {f : Fin r → Fin r'} (hf : f.Injective) (y : RData r) (x : RData r') :
    (y.extend f x).comap f = y := by
  ext i
  · exact hf.extend_apply _ _ i
  · rfl
  · rfl

theorem extend_extend {f : Fin r → Fin r'} (hf : f.Injective) (y z : RData r) (x : RData r') :
    z.extend f (y.extend f x) = z.extend f x :=
  RData.ext (congrArg Data.regs (Data.extend_extend hf y.toData z.toData x.toData)) rfl rfl

theorem extend_comap {f : Fin r → Fin r'} (hf : f.Injective) (x : RData r') :
    (x.comap f).extend f x = x :=
  RData.ext (congrArg Data.regs (Data.extend_comap hf x.toData)) rfl rfl

theorem extend_set {f : Fin r → Fin r'} (hf : f.Injective) (y : RData r) (x : RData r')
    (i : Fin r) (v : ℕ) :
    (y.set i v).extend f x = (y.extend f x).set (f i) v :=
  RData.ext (congrArg Data.regs (Data.extend_set hf y.toData x.toData i v)) rfl rfl

theorem extend_write (f : Fin r → Fin r') (y : RData r) (x : RData r') (a v : ℕ) :
    (y.write a v).extend f x = (y.extend f x).write a v := rfl

theorem extend_regs_apply {f : Fin r → Fin r'} (hf : f.Injective) (y : RData r) (x : RData r')
    (i : Fin r) :
    (y.extend f x).regs (f i) = y.regs i :=
  hf.extend_apply _ _ i

theorem extend_regs_of_notMem {f : Fin r → Fin r'} (y : RData r) (x : RData r') {j : Fin r'}
    (hj : j ∉ Set.range f) :
    (y.extend f x).regs j = x.regs j :=
  Function.extend_apply' _ _ _ hj

theorem extend_regs_of_forall_ne {f : Fin r → Fin r'} (y : RData r) (x : RData r') (i : Fin r')
    (hi : ∀ j, f j ≠ i) :
    (y.extend f x).regs i = x.regs i :=
  extend_regs_of_notMem y x (by rintro ⟨j, hj⟩; exact hi j hj)

theorem Bounded.comap {w : ℕ} {x : RData r'} (hx : x.Bounded w) (f : Fin r → Fin r') :
    (x.comap f).Bounded w :=
  ⟨⟨fun i => hx.regs_fits (f i), hx.1.2⟩, hx.2.1, hx.2.2⟩

theorem Bounded.extend {f : Fin r → Fin r'} {w : ℕ} {y : RData r} {x : RData r'}
    (hf : f.Injective) (hy : y.Bounded w) (hx : x.Bounded w) :
    (y.extend f x).Bounded w := by
  refine ⟨⟨fun j => ?_, hy.1.2⟩, hy.2.1, hy.2.2⟩
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    change (y.extend f x).regs (f i) < 2 ^ w
    rw [extend_regs_apply hf]
    exact hy.regs_fits i
  · change Function.extend f y.regs x.regs j < 2 ^ w
    rw [Function.extend_apply' _ _ _ hj]
    exact hx.regs_fits j

end RData

/-- Rename registers in `RCode B r` along `f : Fin r → Fin r'`. -/
def RCode.rename (f : Fin r → Fin r') : RCode B r → RCode B r'
  | .op o => .op (o.rename f)
  | .seq c₁ c₂ => .seq (c₁.rename f) (c₂.rename f)
  | .branch c pos neg => .branch (c.rename f) (pos.rename f) (neg.rename f)
  | .loop c body => .loop (c.rename f) (body.rename f)
  | .rand dst src => .rand (f dst) (f src)
  | .grow dst => .grow (f dst)
  | .shrink => .shrink

@[simp] theorem RCode.size_rename (f : Fin r → Fin r') (c : RCode B r) :
    (c.rename f).size = c.size := by
  induction c <;> simp_all [RCode.rename]

@[simp] theorem RCode.readsWidth_rename (f : Fin r → Fin r') (c : RCode B r) :
    (c.rename f).ReadsWidth ↔ c.ReadsWidth := by
  induction c with
  | op o => cases o <;> rfl
  | seq _ _ ih₁ ih₂ | branch _ _ _ ih₁ ih₂ => simp [RCode.rename, RCode.ReadsWidth, ih₁, ih₂]
  | loop _ _ ih => exact ih
  | rand _ _ | grow _ | shrink => rfl

/-- Evaluating a renamed instruction on `RData r'` commutes with `RData.comap` and `RData.extend`.
-/
theorem evalResizable_rename {f : Fin r → Fin r'} (hf : f.Injective) (o : Op B r) (w : ℕ)
    (x : RData r') :
    evalResizable w (o.rename f) x =
      (evalResizable w o (x.comap f)).map (fun y => y.extend f x) := by
  have hput {d : Fin r} {v : ℕ} :
      x.put w (f d) v = ((x.comap f).put w d v).map (fun y => y.extend f x) := by
    unfold RData.put
    split <;> simp [RData.extend_set hf, RData.extend_comap hf]
  cases o with
  | const => exact hput
  | copy d s =>
    simp [Op.rename, evalResizable, RData.extend_set hf, RData.extend_comap hf]
  | alu g d args =>
    change (B.interp w g ((x.comap f).regs ∘ args)).bind (x.put w (f d)) =
      ((B.interp w g ((x.comap f).regs ∘ args)).bind ((x.comap f).put w d)).map _
    cases B.interp w g ((x.comap f).regs ∘ args) with
    | none => rfl
    | some v => exact hput
  | load d a =>
    dsimp only [Op.rename, evalResizable, RData.comap_regs, RData.comap_frontier]
    by_cases hlt : x.regs (f a) < x.frontier <;>
      simp [hlt, RData.extend_set hf, RData.extend_comap hf]
  | store a s =>
    dsimp only [Op.rename, evalResizable, RData.comap_regs, RData.comap_frontier]
    by_cases hlt : x.regs (f a) < x.frontier <;>
      simp [hlt, RData.extend_write, RData.extend_comap hf]

/-- **Demonic execution register renaming (`RDemonicExec.rename`).**
Lifts `RDemonicExec` along any injective register embedding `f : Fin r → Fin r'`, preserving all
unmapped registers outside `Set.range f`. -/
theorem RDemonicExec.rename {f : Fin r → Fin r'} (hf : f.Injective) {w L_peak T : ℕ}
    {c : RCode B r} {x : RData r'} {P : RData r → Prop}
    (h : RDemonicExec w L_peak c (x.comap f) T P) :
    RDemonicExec w L_peak (c.rename f) x T (fun z => ∃ y, P y ∧ z = y.extend f x) := by
  generalize hx : x.comap f = x₀ at h
  induction h generalizing x with subst hx
  | @op o _ y P hL he hp =>
    refine .op hL (by rw [evalResizable_rename hf, he]; rfl) ⟨y, hp, rfl⟩
  | @grow dst _ P hL hfit hp =>
    refine .grow hL hfit fun mem' hdem => ?_
    refine ⟨⟨Function.update (x.comap f).regs dst x.frontier, mem', x.frontier + 1⟩, hp mem' hdem,
      ?_⟩
    have hd := (Data.extend_set hf (x.toData.comap f) x.toData dst x.frontier).trans
      (congrArg (fun d => d.set (f dst) x.frontier) (Data.extend_comap hf x.toData))
    exact RData.ext (congrArg Data.regs hd).symm rfl rfl
  | @shrink _ P hL hk hp =>
    refine .shrink hL hk ⟨⟨(x.comap f).regs, clear x.mem (x.frontier - 1) 1, x.frontier - 1⟩, hp,
      ?_⟩
    exact RData.ext (congrArg Data.regs (Data.extend_comap hf x.toData)).symm rfl rfl
  | @rand dst src _ P hL hfit hp =>
    refine .rand hL hfit fun v hv => ⟨(x.comap f).set dst v, hp v hv, ?_⟩
    rw [RData.extend_set hf, RData.extend_comap hf]
  | seq _ _ ih₁ ih₂ =>
    refine .seq (ih₁ rfl) fun z ⟨y₁, hy₁, hz⟩ => ?_
    subst hz
    refine (ih₂ y₁ hy₁ (RData.comap_extend hf y₁ x)).mono le_rfl fun w ⟨y₂, hy₂, hw⟩ => ?_
    rw [RData.extend_extend hf] at hw
    exact ⟨y₂, hy₂, hw⟩
  | branch_pos hc _ ih =>
    exact .branch_pos ((Cond.holds_rename _ _).2 hc) (ih rfl)
  | branch_neg hc _ ih =>
    exact .branch_neg (fun h' => hc ((Cond.holds_rename _ _).1 h')) (ih rfl)
  | loop_exit hL hc hp =>
    exact .loop_exit hL (fun h' => hc ((Cond.holds_rename _ _).1 h'))
      ⟨x.comap f, hp, (RData.extend_comap hf x).symm⟩
  | loop_iter hc _ _ ihb ihl =>
    refine .loop_iter ((Cond.holds_rename _ _).2 hc) (ihb rfl) fun z ⟨y₁, hy₁, hz⟩ => ?_
    subst hz
    refine (ihl y₁ hy₁ (RData.comap_extend hf y₁ x)).mono le_rfl fun w ⟨y₂, hy₂, hw⟩ => ?_
    rw [RData.extend_extend hf] at hw
    exact ⟨y₂, hy₂, hw⟩
  | mono _ hT hPQ ih =>
    exact (ih rfl).mono hT fun z ⟨y, hy, hz⟩ => ⟨y, hPQ y hy, hz⟩

/-- Deterministic postcondition specialization of `RDemonicExec.rename`. -/
theorem RDemonicExec.rename_eq {f : Fin r → Fin r'} (hf : f.Injective) {w L_peak T : ℕ}
    {c : RCode B r} {x : RData r'} {y : RData r}
    (h : RDemonicExec w L_peak c (x.comap f) T (· = y)) :
    RDemonicExec w L_peak (c.rename f) x T (· = y.extend f x) :=
  (h.rename hf).mono le_rfl fun _ ⟨_, rfl, hz⟩ => hz

end Cslib.WordRAM.Resizable
