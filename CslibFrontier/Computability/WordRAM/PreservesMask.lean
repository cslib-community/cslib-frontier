/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Structured

/-!
# Reflected register-preservation and width-read checks for word-RAM code

Proving `∀ i : Fin r, P i → c.Preserves i` by `decide` runs `Nat.decidableForallFin` `r` times
across `c`, taking `O(r · |c|)` reductions and exceeding the default `maxRecDepth` once `r`
reaches a few hundred registers. Likewise, synthesizing `Decidable c.ReadsWidth` walks the full
syntax tree of `c` in the elaborator before kernel reduction can run.

This module provides single-pass `O(|c|)` structural reflections:

* `Cslib.WordRAM.Code.preservesAll : (Fin r → Bool) → Code B r → Bool`: single-pass `Bool` check
  evaluating a predicate only on the destination registers written inside `c`.
* `Cslib.WordRAM.Code.writeStart` / `Cslib.WordRAM.Code.writeEnd`: minimum and strict upper bound
  (`max + 1`) of written register indices using small-`ℕ` `min` and `max`.
* `Cslib.WordRAM.Code.readsWidthBool : Code B r → Bool`: reflected `Bool` check equivalent to
  `Code.ReadsWidth`.

## Main definitions

* `Cslib.WordRAM.Op.preservesAll`, `Cslib.WordRAM.Code.preservesAll`: single-pass `Bool`
  register-preservation check.
* `Cslib.WordRAM.Op.writeStart`, `Cslib.WordRAM.Op.writeEnd`, `Cslib.WordRAM.Code.writeStart`,
  `Cslib.WordRAM.Code.writeEnd`: contiguous register-write interval bounds.
* `Cslib.WordRAM.Op.readsWidthBool`, `Cslib.WordRAM.Code.readsWidthBool`: reflected width-read
  check.

## Main results

* `Cslib.WordRAM.Code.preservesAll_eq_true_iff`,
  `Cslib.WordRAM.Code.preserves_of_preservesAllPred`,
  `Cslib.WordRAM.Code.preservesAll_rename_of_false`: soundness, completeness, and renamed-bank
  elimination for `preservesAll`.
* `Cslib.WordRAM.Code.preserves_of_writeStart`, `Cslib.WordRAM.Code.preserves_of_writeEnd`:
  interval register-preservation bounds.
* `Cslib.WordRAM.Code.readsWidthBool_eq_true_iff`,
  `Cslib.WordRAM.Code.not_readsWidth_of_readsWidthBool`: reflected width-independence rules.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r r' : ℕ}

namespace Op

/-- Returns `true` iff `o` does not write a register satisfying `keep`. -/
def preservesAll (keep : Fin r → Bool) (o : Op B r) : Bool :=
  match o.dest with
  | some d => !(keep d)
  | none => true

/-- Minimum written register index of `o`, or `r` for `store`. -/
def writeStart (o : Op B r) : ℕ :=
  match o.dest with
  | some d => d.val
  | none => r

/-- Strict upper bound (`d.val + 1`) on the register index written by `o`, or `0` for `store`. -/
def writeEnd (o : Op B r) : ℕ :=
  match o.dest with
  | some d => d.val + 1
  | none => 0

/-- Returns `true` iff `o` observes the physical word size `w`. -/
def readsWidthBool : Op B r → Bool
  | .alu f _ _ => decide (B.ReadsWidth f)
  | _ => false

/-- `o.readsWidthBool = true` holds iff `o.ReadsWidth`. -/
theorem readsWidthBool_eq_true_iff (o : Op B r) : o.readsWidthBool = true ↔ o.ReadsWidth := by
  cases o <;> simp [readsWidthBool, Op.ReadsWidth]

private theorem readsWidthBool_rename (f : Fin r → Fin r') (o : Op B r) :
    (o.rename f).readsWidthBool = o.readsWidthBool := by
  cases o <;> rfl

private theorem dest_rename (f : Fin r → Fin r') (o : Op B r) :
    (o.rename f).dest = o.dest.map f := by
  cases o <;> rfl

private theorem preservesAll_rename (keep : Fin r' → Bool) (f : Fin r → Fin r') (o : Op B r) :
    (o.rename f).preservesAll keep = o.preservesAll (keep ∘ f) := by
  simp only [preservesAll, dest_rename]
  cases o.dest <;> rfl

end Op

namespace Code

/-! ## Single-pass `Bool` preservation predicate (`preservesAll`) -/

/-- Single-pass `Bool` check over `Fin r`: returns `true` iff no instruction of `c` writes a
register `d` with `keep d = true`. Unlike `Nat.decidableForallFin`, this visits `c` once and
evaluates `keep` only on written destinations (`O(|c|)` instead of `O(r · |c|)`). -/
def preservesAll (keep : Fin r → Bool) : Code B r → Bool
  | .op o => o.preservesAll keep
  | .seq c₁ c₂ => c₁.preservesAll keep && c₂.preservesAll keep
  | .branch _ pos neg => pos.preservesAll keep && neg.preservesAll keep
  | .loop _ body => body.preservesAll keep
  | .rand dst _ => !(keep dst)

/-- `c.preservesAll keep = true` matches preserving every register with `keep i = true`. -/
theorem preservesAll_eq_true_iff (keep : Fin r → Bool) (c : Code B r) :
    c.preservesAll keep = true ↔ ∀ i : Fin r, keep i = true → c.Preserves i := by
  induction c with
  | op o =>
    simp only [preservesAll, Op.preservesAll, Preserves]
    cases o.dest with
    | none => simp
    | some d =>
      simp only [Bool.not_eq_true', ne_eq, Option.some.injEq]
      exact ⟨fun h i hi heq => by subst heq; simp [hi] at h,
        fun h => Bool.eq_false_iff.mpr fun hd => h d hd rfl⟩
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [preservesAll, Bool.and_eq_true, Preserves, ih₁, ih₂]
    exact ⟨fun ⟨h₁, h₂⟩ i hi => ⟨h₁ i hi, h₂ i hi⟩,
      fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩⟩
  | branch _ pos neg ihp ihn =>
    simp only [preservesAll, Bool.and_eq_true, Preserves, ihp, ihn]
    exact ⟨fun ⟨h₁, h₂⟩ i hi => ⟨h₁ i hi, h₂ i hi⟩,
      fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩⟩
  | loop _ body ih => exact ih
  | rand dst _ =>
    simp only [preservesAll, Preserves, Bool.not_eq_true']
    exact ⟨fun h i hi heq => by subst heq; simp [hi] at h,
      fun h => Bool.eq_false_iff.mpr fun hd => h dst hd rfl⟩

/-- Drop-in replacement for `∀ i : Fin r, P i → c.Preserves i := by decide`: evaluates `P` only on
the destination registers written inside `c`, never iterating over all `r` elements of `Fin r`. -/
theorem preserves_of_preservesAllPred {P : Fin r → Prop} [DecidablePred P] {c : Code B r}
    (h : c.preservesAll (fun i => decide (P i)) = true) :
    ∀ i : Fin r, P i → c.Preserves i :=
  fun i hi => (preservesAll_eq_true_iff _ c).mp h i (decide_eq_true hi)

/-- Register renaming pulls `keep` back along `f` without unfolding `c`. -/
@[simp]
theorem preservesAll_rename (keep : Fin r' → Bool) (f : Fin r → Fin r') (c : Code B r) :
    (c.rename f).preservesAll keep = c.preservesAll (keep ∘ f) := by
  induction c with
  | op o => exact o.preservesAll_rename keep f
  | seq c₁ c₂ ih₁ ih₂ => simp [rename, preservesAll, ih₁, ih₂]
  | branch _ pos neg ihp ihn => simp [rename, preservesAll, ihp, ihn]
  | loop _ body ih => exact ih
  | rand _ _ => rfl

@[simp]
private theorem preservesAll_const_false (c : Code B r) :
    c.preservesAll (fun _ => false) = true := by
  rw [preservesAll_eq_true_iff]
  intro _ h
  cases h

/-- `preservesAll` on a renamed subprogram is `true` without unfolding the callee whenever the
register bank `f` is disjoint from `keep`. -/
theorem preservesAll_rename_of_false {keep : Fin r' → Bool} {f : Fin r → Fin r'}
    (hf : ∀ j : Fin r, keep (f j) = false) (c : Code B r) :
    (c.rename f).preservesAll keep = true := by
  rw [preservesAll_rename, show keep ∘ f = fun _ => false from funext hf, preservesAll_const_false]

/-! ## Interval bounds (`writeStart` / `writeEnd`) -/

/-- Minimum written register index (or `r` when `c` writes no registers). -/
def writeStart : Code B r → ℕ
  | .op o => o.writeStart
  | .seq c₁ c₂ => min c₁.writeStart c₂.writeStart
  | .branch _ pos neg => min pos.writeStart neg.writeStart
  | .loop _ body => body.writeStart
  | .rand dst _ => dst.val

/-- Strict upper bound `max d + 1` on written register indices (or `0` when `c` writes none). -/
def writeEnd : Code B r → ℕ
  | .op o => o.writeEnd
  | .seq c₁ c₂ => max c₁.writeEnd c₂.writeEnd
  | .branch _ pos neg => max pos.writeEnd neg.writeEnd
  | .loop _ body => body.writeEnd
  | .rand dst _ => dst.val + 1

private theorem preserves_of_lt_writeStart {c : Code B r} {i : Fin r} (hi : i.val < c.writeStart) :
    c.Preserves i := by
  induction c with
  | op o =>
    simp only [Preserves, writeStart, Op.writeStart] at hi ⊢
    cases h : o.dest with
    | none => simp
    | some d =>
      simp only [h, ne_eq, Option.some.injEq] at hi ⊢
      exact fun heq => Nat.ne_of_lt hi (congrArg Fin.val heq).symm
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [writeStart, lt_min_iff] at hi
    exact ⟨ih₁ hi.1, ih₂ hi.2⟩
  | branch _ pos neg ihp ihn =>
    simp only [writeStart, lt_min_iff] at hi
    exact ⟨ihp hi.1, ihn hi.2⟩
  | loop _ body ih => exact ih hi
  | rand _ _ =>
    exact fun h => Nat.ne_of_lt hi (congrArg Fin.val h).symm

/-- Every register strictly below `lo` is preserved when `lo ≤ c.writeStart`. -/
theorem preserves_of_writeStart {c : Code B r} {lo : ℕ} (h : lo ≤ c.writeStart)
    {i : Fin r} (hi : i.val < lo) : c.Preserves i :=
  preserves_of_lt_writeStart (Nat.lt_of_lt_of_le hi h)

private theorem preserves_of_writeEnd_le {c : Code B r} {i : Fin r} (hi : c.writeEnd ≤ i.val) :
    c.Preserves i := by
  induction c with
  | op o =>
    simp only [Preserves, writeEnd, Op.writeEnd] at hi ⊢
    cases h : o.dest with
    | none => simp
    | some d =>
      simp only [h, ne_eq, Option.some.injEq] at hi ⊢
      exact fun heq => absurd (congrArg Fin.val heq) (by omega)
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [writeEnd, max_le_iff] at hi
    exact ⟨ih₁ hi.1, ih₂ hi.2⟩
  | branch _ pos neg ihp ihn =>
    simp only [writeEnd, max_le_iff] at hi
    exact ⟨ihp hi.1, ihn hi.2⟩
  | loop _ body ih => exact ih hi
  | rand _ _ =>
    intro h
    simp only [writeEnd] at hi
    have := congrArg Fin.val h
    omega

/-- Every register at or above `hi` is preserved when `c.writeEnd ≤ hi`. -/
theorem preserves_of_writeEnd {c : Code B r} {hi : ℕ} (h : c.writeEnd ≤ hi)
    {i : Fin r} (hge : hi ≤ i.val) : c.Preserves i :=
  preserves_of_writeEnd_le (h.trans hge)

/-! ## Reflected `readsWidthBool` and compositional rules -/

/-- Structural `Bool` check determining whether `c` reads the physical word width `w`. -/
def readsWidthBool : Code B r → Bool
  | .op o => o.readsWidthBool
  | .seq c₁ c₂ => c₁.readsWidthBool || c₂.readsWidthBool
  | .branch _ pos neg => pos.readsWidthBool || neg.readsWidthBool
  | .loop _ body => body.readsWidthBool
  | .rand _ _ => false

/-- `c.readsWidthBool = true` holds iff `c.ReadsWidth`. -/
theorem readsWidthBool_eq_true_iff (c : Code B r) : c.readsWidthBool = true ↔ c.ReadsWidth := by
  induction c with
  | op o => exact o.readsWidthBool_eq_true_iff
  | seq _ _ ih₁ ih₂ => simp [readsWidthBool, ReadsWidth, ih₁, ih₂]
  | branch _ _ _ ihp ihn => simp [readsWidthBool, ReadsWidth, ihp, ihn]
  | loop _ _ ih => exact ih
  | rand _ _ => simp [readsWidthBool, ReadsWidth]

/-- Soundness for the reflected width check. -/
theorem not_readsWidth_of_readsWidthBool {c : Code B r} (h : c.readsWidthBool = false) :
    ¬c.ReadsWidth :=
  fun hc => Bool.false_ne_true (h.symm.trans (c.readsWidthBool_eq_true_iff.mpr hc))

/-- Register renaming preserves `readsWidthBool` without unfolding `c`. -/
@[simp]
theorem readsWidthBool_rename (f : Fin r → Fin r') (c : Code B r) :
    (c.rename f).readsWidthBool = c.readsWidthBool := by
  induction c with
  | op o => exact o.readsWidthBool_rename f
  | seq _ _ ih₁ ih₂ => simp [rename, readsWidthBool, ih₁, ih₂]
  | branch _ _ _ ihp ihn => simp [rename, readsWidthBool, ihp, ihn]
  | loop _ _ ih => exact ih
  | rand _ _ => rfl

end Code

end Cslib.WordRAM
