/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.AuxPDA.Surface
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

/-!
# Bounded-space surface enumeration and decidable surface transitions

A *bounded-space surface configuration* (`Turing.AuxPDA.BoundedSurfaceCfg`) restricts the work-tape
cells and head positions of a `Turing.AuxPDA.SurfaceCfg` to the symmetric window `[-s, s]`
(`Turing.window s`). This produces a concrete finite type with:

* an exact embedding `BoundedSurfaceCfg.toSurface` onto `{sc | sc.storage.FitsIn (fun _ => s)}`;
* a computable mixed-radix bijection `boundedSurfaceEquivFin` onto `Fin (boundedSurfaceCard …)`,
  giving `input.length + 2 ≤ boundedSurfaceCard … ≤ surfaceCfgBound … (k * s)` and therefore
  polynomial cardinality in `n` for logarithmic space `s(n) = O(log n)`
  (`boundedSurfaceCard_log_polynomiallyBounded`);
* decidable local transition predicates `BoundedStayStep`, `BoundedPushStep`, `BoundedPopStep`, and
  `BoundedPushPopStep` via `applyBoundedTapes?`, together with `Decidable` transport through
  `AuxPDA.withEmptyStackHalt`.

This is original formalization infrastructure for Work Package 4 of cslib-frontier #7920, supplying
the finite surface-configuration indexing consumed by the balanced-depth semi-unbounded circuit
compiler.

## Main definitions

* `Turing.AuxPDA.BoundedSurfaceCfg`: surface configurations restricted to `Turing.window s`.
* `Turing.AuxPDA.BoundedSurfaceCfg.toSurface`, `Turing.AuxPDA.BoundedSurfaceCfg.ofSurface`,
  `Turing.AuxPDA.initBoundedSurface`: bijection with `FitsIn (fun _ => s)` surface configurations.
* `Turing.AuxPDA.boundedSurfaceCard`, `Turing.AuxPDA.boundedSurfaceEquivFin`: explicit computable
  mixed-radix `Fin` indexing.
* `Turing.AuxPDA.applyBoundedTapes?`, `Turing.AuxPDA.BoundedStayStep`,
  `Turing.AuxPDA.BoundedPushStep`, `Turing.AuxPDA.BoundedPopStep`,
  `Turing.AuxPDA.BoundedPushPopStep`: bounded surface transitions with computable `Decidable`
  instances.

## Main results

* `Turing.AuxPDA.BoundedSurfaceCfg.toSurface_fitsIn`,
  `Turing.AuxPDA.BoundedSurfaceCfg.toSurface_injective`: exact correspondence with `FitsIn`.
* `Turing.AuxPDA.input_length_add_two_le_boundedSurfaceCard`,
  `Turing.AuxPDA.boundedSurfaceCard_le_surfaceCfgBound`,
  `Turing.AuxPDA.boundedSurfaceCard_log_polynomiallyBounded`: lower and upper polynomial cardinality
  bounds.
* `Turing.AuxPDA.applyBoundedTapes?_eq_some_iff`: exact agreement between window-checked bounded
  updates and `applySurfaceTapes`.
-/

public section

namespace Turing.AuxPDA

/-! ### Bounded-space surface configurations -/

/-- A surface configuration of a binary `k`-tape `AuxPDA` on `input` whose work-tape heads and
non-blank cells are restricted to `Turing.window s = [-s, s]`. -/
@[ext]
structure BoundedSurfaceCfg (k : ℕ) (StackSym State : Type*) (input : List Bool) (s : ℕ) where
  /-- Input head position (shifted by one, matching `SurfaceCfg.inputPos`). -/
  inputPos : Fin (input.length + 2)
  /-- Control state (`none` when halted). -/
  state : Option State
  /-- Work-tape contents on the bounded window `[-s, s]`. -/
  workTapes : Fin k → Turing.window s → Option Bool
  /-- Work-tape head positions within `[-s, s]`. -/
  workTapePos : Fin k → Turing.window s
  /-- Top symbol of the pushdown stack, or `none` when empty. -/
  topSym : Option StackSym
  /-- Three-value acceptance summary of the write-only binary output tape. -/
  outputSummary : OutputSummary

namespace BoundedSurfaceCfg

variable {k : ℕ} {StackSym State : Type*} {input : List Bool} {s : ℕ}

instance [DecidableEq StackSym] [DecidableEq State] :
    DecidableEq (BoundedSurfaceCfg k StackSym State input s) := fun a b =>
  if h1 : a.inputPos = b.inputPos then
    if h2 : a.state = b.state then
      if h3 : a.workTapes = b.workTapes then
        if h4 : a.workTapePos = b.workTapePos then
          if h5 : a.topSym = b.topSym then
            if h6 : a.outputSummary = b.outputSummary then
              isTrue (BoundedSurfaceCfg.ext h1 h2 h3 h4 h5 h6)
            else isFalse fun h => h6 (congrArg outputSummary h)
          else isFalse fun h => h5 (congrArg topSym h)
        else isFalse fun h => h4 (congrArg workTapePos h)
      else isFalse fun h => h3 (congrArg workTapes h)
    else isFalse fun h => h2 (congrArg state h)
  else isFalse fun h => h1 (congrArg inputPos h)

/-- Embed a bounded-space surface configuration into `SurfaceCfg`, padding cells outside
`Turing.window s` with blanks (`none`). -/
@[expose] def toSurface (b : BoundedSurfaceCfg k StackSym State input s) :
    SurfaceCfg k StackSym State input where
  inputPos := b.inputPos
  storage :=
    { state := b.state
      workTapes := fun i z => if hz : z ∈ Turing.window s then b.workTapes i ⟨z, hz⟩ else none
      workTapePos := fun i => (b.workTapePos i).val }
  topSym := b.topSym
  outputSummary := b.outputSummary

/-- Every embedded bounded surface configuration fits in the uniform window `fun _ => s`. -/
theorem toSurface_fitsIn (b : BoundedSurfaceCfg k StackSym State input s) :
    b.toSurface.storage.FitsIn (fun _ => s) := by
  refine ⟨fun j => Turing.mem_window.mp (b.workTapePos j).property, fun j z hz => ?_⟩
  by_contra hout
  have hnotmem : z ∉ Turing.window s := fun hm => hout (Turing.mem_window.mp hm)
  simp [toSurface, hnotmem] at hz

/-- Embedding into `SurfaceCfg` is injective. -/
theorem toSurface_injective :
    Function.Injective (toSurface (k := k) (StackSym := StackSym) (State := State)
      (input := input) (s := s)) := by
  intro a b hab
  have hpos : a.inputPos = b.inputPos := congrArg SurfaceCfg.inputPos hab
  have hst : a.state = b.state := congrArg (fun sc => sc.storage.state) hab
  have htop : a.topSym = b.topSym := congrArg SurfaceCfg.topSym hab
  have hout : a.outputSummary = b.outputSummary := congrArg SurfaceCfg.outputSummary hab
  have hwt : a.workTapes = b.workTapes := by
    funext i z
    have hz := congrFun (congrFun (congrArg (fun sc => sc.storage.workTapes) hab) i) z.val
    simpa only [toSurface, z.property, ↓reduceDIte] using hz
  have hwp : a.workTapePos = b.workTapePos := by
    funext i
    exact Subtype.ext (congrFun (congrArg (fun sc => sc.storage.workTapePos) hab) i)
  exact BoundedSurfaceCfg.ext hpos hst hwt hwp htop hout

/-- Restrict a surface configuration fitting in `fun _ => s` to `BoundedSurfaceCfg`. -/
@[expose] def ofSurface (sc : SurfaceCfg k StackSym State input)
    (h : sc.storage.FitsIn (fun _ => s)) :
    BoundedSurfaceCfg k StackSym State input s where
  inputPos := sc.inputPos
  state := sc.storage.state
  workTapes := fun i z => sc.storage.workTapes i z.val
  workTapePos := fun i => ⟨sc.storage.workTapePos i, Turing.mem_window.mpr (h.pos_le i)⟩
  topSym := sc.topSym
  outputSummary := sc.outputSummary

@[simp]
theorem toSurface_ofSurface (sc : SurfaceCfg k StackSym State input)
    (h : sc.storage.FitsIn (fun _ => s)) :
    (ofSurface sc h).toSurface = sc := by
  refine SurfaceCfg.ext rfl (Turing.Storage.ext rfl (funext fun i => funext fun z => ?_) rfl)
    rfl rfl
  dsimp only [toSurface, ofSurface]
  split_ifs with hz
  · rfl
  · symm
    by_contra hne
    exact hz (Turing.mem_window.mpr (h.cell_le i z hne))

@[simp]
theorem ofSurface_toSurface (b : BoundedSurfaceCfg k StackSym State input s) :
    ofSurface b.toSurface b.toSurface_fitsIn = b :=
  toSurface_injective (toSurface_ofSurface b.toSurface b.toSurface_fitsIn)

/-- The input symbol under the head of a bounded surface configuration. -/
@[expose] def inputSymbol (b : BoundedSurfaceCfg k StackSym State input s) : Option Bool :=
  b.toSurface.inputSymbol

/-- The work-tape symbols under the heads of a bounded surface configuration. -/
@[expose] def workTapeSymbols (b : BoundedSurfaceCfg k StackSym State input s) (i : Fin k) :
    Option Bool :=
  b.workTapes i (b.workTapePos i)

lemma workTapeSymbols_eq_toSurface (b : BoundedSurfaceCfg k StackSym State input s) :
    b.workTapeSymbols = b.toSurface.workTapeSymbols := by
  funext i
  simp [workTapeSymbols, SurfaceCfg.workTapeSymbols, toSurface]

/-- A bounded surface configuration is accepting when halted with output summary `.accept`. -/
abbrev IsAccepting (b : BoundedSurfaceCfg k StackSym State input s) : Prop :=
  b.state = none ∧ b.outputSummary = .accept

/-- An accepting bounded surface configuration with an empty stack (`topSym = none`). -/
abbrev IsAcceptingEmpty (b : BoundedSurfaceCfg k StackSym State input s) : Prop :=
  b.IsAccepting ∧ b.topSym = none

end BoundedSurfaceCfg

/-- The initial bounded surface configuration of `M` on `input` within window `[-s, s]`. -/
@[expose] def initBoundedSurface {k : ℕ} {StackSym State : Type*}
    (M : AuxPDA k Bool StackSym State) (input : List Bool) (s : ℕ) :
    BoundedSurfaceCfg k StackSym State input s where
  inputPos := ⟨1, by omega⟩
  state := some M.q₀
  workTapes := fun _ _ => none
  workTapePos := fun _ => ⟨0, Turing.mem_window.mpr (Nat.zero_le s)⟩
  topSym := none
  outputSummary := .empty

@[simp]
theorem toSurface_initBoundedSurface {k : ℕ} {StackSym State : Type*}
    (M : AuxPDA k Bool StackSym State) (input : List Bool) (s : ℕ) :
    (initBoundedSurface M input s).toSurface = M.initSurface input := by
  refine SurfaceCfg.ext ?_ (Turing.Storage.ext rfl ?_ rfl) rfl rfl
  · ext
    change 1 = (1 : ℕ) % (input.length + 2)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · funext i z
    simp [initBoundedSurface, BoundedSurfaceCfg.toSurface, initSurface, initCfg, Cfg.init,
      Cfg.surface, Turing.Cfg.init, Turing.Cfg.storage]

/-! ### Computable mixed-radix `Fin` indexing and polynomial cardinality bounds -/

/-- Explicit computable bijection between the symmetric window `[-s, s]` and `Fin (2 * s + 1)`. -/
private def windowEquivFin (s : ℕ) : Turing.window s ≃ Fin (2 * s + 1) where
  toFun z := ⟨(z.val + s).toNat, by
    have hz := Finset.mem_Icc.mp z.property
    omega⟩
  invFun i := ⟨(i.val : ℤ) - s, Finset.mem_Icc.mpr (by omega)⟩
  left_inv z := by
    ext
    dsimp only
    have hz := Finset.mem_Icc.mp z.property
    omega
  right_inv i := by
    ext
    dsimp only
    omega

/-- Explicit computable bijection between `OutputSummary` and `Fin 3`. -/
private def outputSummaryEquivFin : OutputSummary ≃ Fin 3 where
  toFun
    | .empty => ⟨0, by decide⟩
    | .accept => ⟨1, by decide⟩
    | .other => ⟨2, by decide⟩
  invFun
    | ⟨0, _⟩ => .empty
    | ⟨1, _⟩ => .accept
    | ⟨2, _⟩ => .other
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Explicit computable bijection between `Option α` and `Fin (m + 1)` from `α ≃ Fin m`. -/
private def optionEquivFin {α : Type*} {m : ℕ} (e : α ≃ Fin m) : Option α ≃ Fin (m + 1) where
  toFun
    | none => ⟨0, Nat.succ_pos m⟩
    | some a => ⟨(e a).val + 1, Nat.succ_lt_succ (e a).isLt⟩
  invFun i :=
    match i with
    | ⟨0, _⟩ => none
    | ⟨n + 1, h⟩ => some (e.symm ⟨n, Nat.lt_of_succ_lt_succ h⟩)
  left_inv x := by
    cases x with
    | none => rfl
    | some a => simp
  right_inv i := by
    rcases i with ⟨n, hn⟩
    cases n with
    | zero => rfl
    | succ n => simp

/-- Explicit computable bijection between `Option Bool` and `Fin 3`. -/
private def optionBoolEquivFin : Option Bool ≃ Fin 3 :=
  optionEquivFin
    { toFun := fun b => if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
      invFun := fun i => i.val == 1
      left_inv := fun b => by cases b <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }

/-- Explicit computable mixed-radix bijection `(Fin k → Fin m) ≃ Fin (m ^ k)`. -/
private def finFunEquivFin : (k m : ℕ) → (Fin k → Fin m) ≃ Fin (m ^ k)
  | 0, _ =>
    { toFun := fun _ => ⟨0, by simp⟩
      invFun := fun _ => Fin.elim0
      left_inv := fun f => funext fun i => i.elim0
      right_inv := fun i => by fin_cases i; rfl }
  | k + 1, m =>
    let split : (Fin (k + 1) → Fin m) ≃ Fin m × (Fin k → Fin m) :=
      { toFun := fun f => (f 0, fun i => f i.succ)
        invFun := fun (a, rest) => Fin.cons a rest
        left_inv := fun f => by
          funext i
          refine Fin.cases ?_ ?_ i <;> simp
        right_inv := fun (a, rest) => by
          ext
          · simp
          · simp }
    split.trans ((Equiv.prodCongr (Equiv.refl _) (finFunEquivFin k m)).trans
      (finProdFinEquiv.trans (finCongr (by rw [pow_succ']))))

/-- Exact cardinality of `BoundedSurfaceCfg k StackSym State input s` when `|StackSym| = mStack`
and `|State| = mState`. -/
@[expose] def boundedSurfaceCard (mStack mState k n s : ℕ) : ℕ :=
  (((((n + 2) * (mState + 1)) * (2 * s + 1) ^ k) * (3 ^ (2 * s + 1)) ^ k) * (mStack + 1)) * 3

/-- Computable mixed-radix bijection indexing every bounded-space surface configuration by
`Fin (boundedSurfaceCard mStack mState k input.length s)`. -/
def boundedSurfaceEquivFin {k mStack mState : ℕ} {StackSym State : Type*}
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s : ℕ) :
    BoundedSurfaceCfg k StackSym State input s ≃
      Fin (boundedSurfaceCard mStack mState k input.length s) :=
  let toTuple : BoundedSurfaceCfg k StackSym State input s ≃
      (((((Fin (input.length + 2) × Option State) × (Fin k → Turing.window s)) ×
        (Fin k → Turing.window s → Option Bool)) × Option StackSym) × OutputSummary) :=
    { toFun := fun b => (((((b.inputPos, b.state), b.workTapePos), b.workTapes), b.topSym),
        b.outputSummary)
      invFun := fun (((((ip, st), wp), wt), top), out) => ⟨ip, st, wt, wp, top, out⟩
      left_inv := fun b => by cases b; rfl
      right_inv := fun (((((_, _), _), _), _), _) => rfl }
  let eStateOpt : Option State ≃ Fin (mState + 1) := optionEquivFin eState
  let eStackOpt : Option StackSym ≃ Fin (mStack + 1) := optionEquivFin eStack
  let eWorkPos : (Fin k → Turing.window s) ≃ Fin ((2 * s + 1) ^ k) :=
    (Equiv.piCongrRight fun _ => windowEquivFin s).trans (finFunEquivFin k (2 * s + 1))
  let eOneTape : (Turing.window s → Option Bool) ≃ Fin (3 ^ (2 * s + 1)) :=
    (Equiv.arrowCongr (windowEquivFin s) optionBoolEquivFin).trans
      (finFunEquivFin (2 * s + 1) 3)
  let eWorkTapes : (Fin k → Turing.window s → Option Bool) ≃ Fin ((3 ^ (2 * s + 1)) ^ k) :=
    (Equiv.piCongrRight fun _ => eOneTape).trans (finFunEquivFin k (3 ^ (2 * s + 1)))
  let e1 := (Equiv.prodCongr (Equiv.refl _) eStateOpt).trans finProdFinEquiv
  let e2 := (Equiv.prodCongr e1 eWorkPos).trans finProdFinEquiv
  let e3 := (Equiv.prodCongr e2 eWorkTapes).trans finProdFinEquiv
  let e4 := (Equiv.prodCongr e3 eStackOpt).trans finProdFinEquiv
  let e5 := (Equiv.prodCongr e4 outputSummaryEquivFin).trans finProdFinEquiv
  toTuple.trans e5

noncomputable instance instFintypeBoundedSurfaceCfg {k : ℕ} {StackSym State : Type*}
    [Fintype StackSym] [Fintype State] {input : List Bool} {s : ℕ} :
    Fintype (BoundedSurfaceCfg k StackSym State input s) :=
  Fintype.ofEquiv _
    (boundedSurfaceEquivFin (Fintype.equivFin StackSym) (Fintype.equivFin State) input s).symm

theorem card_boundedSurfaceCfg {k : ℕ} {StackSym State : Type*}
    [Fintype StackSym] [Fintype State] (input : List Bool) (s : ℕ) :
    Fintype.card (BoundedSurfaceCfg k StackSym State input s) =
      boundedSurfaceCard (Fintype.card StackSym) (Fintype.card State) k input.length s :=
  (Fintype.card_congr
    (boundedSurfaceEquivFin (k := k) (Fintype.equivFin StackSym) (Fintype.equivFin State)
      input s)).trans (Fintype.card_fin _)

/-- The bounded surface-configuration count is always at least `n + 2` (from the input head). -/
theorem input_length_add_two_le_boundedSurfaceCard (mStack mState k n s : ℕ) :
    n + 2 ≤ boundedSurfaceCard mStack mState k n s := by
  unfold boundedSurfaceCard
  have hprod : 0 < (mState + 1) * (2 * s + 1) ^ k * (3 ^ (2 * s + 1)) ^ k * (mStack + 1) * 3 := by
    positivity
  have heq :
      (((((n + 2) * (mState + 1)) * (2 * s + 1) ^ k) * (3 ^ (2 * s + 1)) ^ k) *
        (mStack + 1)) * 3 =
      (n + 2) * ((mState + 1) * (2 * s + 1) ^ k * (3 ^ (2 * s + 1)) ^ k * (mStack + 1) * 3) := by
    ring
  rw [heq]
  exact Nat.le_mul_of_pos_right (n + 2) hprod

/-- The bounded surface-configuration cardinality is at most `surfaceCfgBound … (k * s)`. -/
theorem boundedSurfaceCard_le_surfaceCfgBound {StackSym State : Type*}
    [Fintype StackSym] [Fintype State] (k n s : ℕ) :
    boundedSurfaceCard (Fintype.card StackSym) (Fintype.card State) k n s ≤
      surfaceCfgBound StackSym State k n (k * s) := by
  unfold boundedSurfaceCard surfaceCfgBound Turing.storageBound
  have hcardBool : Fintype.card Bool + 1 = 3 := by decide
  rw [hcardBool]
  have hpow3 : (3 ^ (2 * s + 1)) ^ k = 3 ^ (2 * (k * s) + k) := by
    rw [← pow_mul]
    congr 1
    ring
  have hpowPos : (2 * s + 1) ^ k ≤ (2 * (k * s) + 1) ^ k := by
    cases k with
    | zero => simp
    | succ k' =>
      refine Nat.pow_le_pow_left ?_ _
      have : s ≤ (k' + 1) * s := Nat.le_mul_of_pos_left s (Nat.succ_pos k')
      omega
  rw [hpow3]
  have hrearr1 :
      (((((n + 2) * (Fintype.card State + 1)) * (2 * s + 1) ^ k) * 3 ^ (2 * (k * s) + k)) *
        (Fintype.card StackSym + 1)) * 3 =
      ((n + 2) * (Fintype.card StackSym + 1) * 3 * (Fintype.card State + 1)) *
        ((2 * s + 1) ^ k * 3 ^ (2 * (k * s) + k)) := by ring
  have hrearr2 :
      (n + 2) * (Fintype.card StackSym + 1) * 3 *
        ((Fintype.card State + 1) * ((2 * (k * s) + 1) ^ k * 3 ^ (2 * (k * s) + k))) =
      ((n + 2) * (Fintype.card StackSym + 1) * 3 * (Fintype.card State + 1)) *
        ((2 * (k * s) + 1) ^ k * 3 ^ (2 * (k * s) + k)) := by ring
  rw [hrearr1, hrearr2]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpowPos)

/-- **Polynomial bounded-surface cardinality in logarithmic space**: for `s(n) = c * (log₂ n + 1)`,
`boundedSurfaceCard` is polynomially bounded in `n`. -/
theorem boundedSurfaceCard_log_polynomiallyBounded (mStack mState k c : ℕ) :
    Cslib.PolynomiallyBounded fun n =>
      boundedSurfaceCard mStack mState k n (c * (Nat.log2 n + 1)) := by
  have h := surfaceCfgBound_log_polynomiallyBounded (StackSym := Fin mStack) (State := Fin mState)
    k c
  refine h.mono_of_le fun n => ?_
  simpa only [Fintype.card_fin] using
    boundedSurfaceCard_le_surfaceCfgBound (StackSym := Fin mStack) (State := Fin mState) k n
      (c * (Nat.log2 n + 1))

/-! ### Window-checked tape updates and decidable bounded surface transitions -/

section Transitions

variable {k : ℕ} {StackSym State : Type*} {input : List Bool} {s : ℕ}

/-- Apply a `Turing.Action` to a bounded surface configuration, returning `none` if any work-tape
head steps outside `Turing.window s`. -/
@[expose] def applyBoundedTapes? (act : Turing.Action k Bool State)
    (b : BoundedSurfaceCfg k StackSym State input s) (newTop : Option StackSym) :
    Option (BoundedSurfaceCfg k StackSym State input s) :=
  if h : ∀ i : Fin k, (b.workTapePos i).val + (act.workTapes i).2 ∈ Turing.window s then
    some
      { inputPos := moveInputPos b.inputPos act.inputTape
        state := act.state
        workTapes := fun i z =>
          if z = b.workTapePos i then
            match (act.workTapes i).1 with
            | none => b.workTapes i z
            | some sym => sym
          else b.workTapes i z
        workTapePos := fun i => ⟨(b.workTapePos i).val + (act.workTapes i).2, h i⟩
        topSym := newTop
        outputSummary := b.outputSummary.append act.output }
  else none

private lemma toSurface_applyBoundedTapes_some (act : Turing.Action k Bool State)
    (b : BoundedSurfaceCfg k StackSym State input s) (newTop : Option StackSym)
    (hwin : ∀ i : Fin k, (b.workTapePos i).val + (act.workTapes i).2 ∈ Turing.window s) :
    ({ inputPos := moveInputPos b.inputPos act.inputTape
       state := act.state
       workTapes := fun i z =>
         if z = b.workTapePos i then
           match (act.workTapes i).1 with
           | none => b.workTapes i z
           | some sym => sym
         else b.workTapes i z
       workTapePos := fun i => ⟨(b.workTapePos i).val + (act.workTapes i).2, hwin i⟩
       topSym := newTop
       outputSummary := b.outputSummary.append act.output } :
        BoundedSurfaceCfg k StackSym State input s).toSurface =
      applySurfaceTapes act b.toSurface newTop := by
  refine SurfaceCfg.ext rfl (Turing.Storage.ext rfl (funext fun i => funext fun z => ?_) rfl)
    rfl rfl
  dsimp only [BoundedSurfaceCfg.toSurface, applySurfaceTapes]
  cases hw : (act.workTapes i).1 with
  | none =>
    simp only
    split_ifs <;> rfl
  | some sym =>
    by_cases hz : z ∈ Turing.window s
    · simp only [hz, ↓reduceDIte, Function.update]
      by_cases heq : z = (b.workTapePos i).val
      · simp [heq]
      · have hsub : (⟨z, hz⟩ : Turing.window s) ≠ b.workTapePos i := fun h' =>
          heq (congrArg Subtype.val h')
        simp [heq, hsub]
    · have hne : z ≠ (b.workTapePos i).val := fun h' => hz (h' ▸ (b.workTapePos i).property)
      simp [hz, hne, Function.update]

/-- Window-checked bounded application agrees identically with `applySurfaceTapes` on embedded
surface configurations. -/
theorem applyBoundedTapes?_eq_some_iff (act : Turing.Action k Bool State)
    (b c : BoundedSurfaceCfg k StackSym State input s) (newTop : Option StackSym) :
    applyBoundedTapes? act b newTop = some c ↔
      c.toSurface = applySurfaceTapes act b.toSurface newTop := by
  constructor
  · intro h
    unfold applyBoundedTapes? at h
    split_ifs at h with hwin
    simp only [Option.some.injEq] at h
    subst h
    exact toSurface_applyBoundedTapes_some act b newTop hwin
  · intro h
    have hwin : ∀ i : Fin k, (b.workTapePos i).val + (act.workTapes i).2 ∈ Turing.window s := by
      intro i
      have hpos := congrFun (congrArg (fun sc => sc.storage.workTapePos) h) i
      dsimp only [BoundedSurfaceCfg.toSurface, applySurfaceTapes] at hpos
      rw [← hpos]
      exact (c.workTapePos i).property
    unfold applyBoundedTapes?
    rw [dite_eq_left_of_eq_true (eq_true hwin), Option.some.injEq]
    apply BoundedSurfaceCfg.toSurface_injective
    rw [h]
    exact toSurface_applyBoundedTapes_some act b newTop hwin

/-- Bounded-space height-preserving surface transition (`StayStep` on embedded surfaces). -/
@[expose] def BoundedStayStep (M : AuxPDA k Bool StackSym State)
    (u v : BoundedSurfaceCfg k StackSym State input s) : Prop :=
  M.StayStep u.toSurface v.toSurface

/-- Bounded-space push transition (`PushStep` on embedded surfaces). -/
@[expose] def BoundedPushStep (M : AuxPDA k Bool StackSym State)
    (u : BoundedSurfaceCfg k StackSym State input s) (γ : StackSym)
    (v : BoundedSurfaceCfg k StackSym State input s) : Prop :=
  M.PushStep u.toSurface γ v.toSurface

/-- Bounded-space pop transition (`PopStep` on embedded surfaces). -/
@[expose] def BoundedPopStep (M : AuxPDA k Bool StackSym State)
    (u : BoundedSurfaceCfg k StackSym State input s) (γ : StackSym) (baseTop : Option StackSym)
    (v : BoundedSurfaceCfg k StackSym State input s) : Prop :=
  M.PopStep u.toSurface γ baseTop v.toSurface

/-- Bounded-space matched push-pop pair wrapping `(u', v')` into `(u, v)`. -/
@[expose] def BoundedPushPopStep (M : AuxPDA k Bool StackSym State)
    (u u' v' v : BoundedSurfaceCfg k StackSym State input s) : Prop :=
  ∃ γ : StackSym, M.BoundedPushStep u γ u' ∧ M.BoundedPopStep v' γ u.topSym v

end Transitions

/-! ### Computable finiteness of actions and decidability of bounded surface steps -/

section DecidableTransitions

variable {k : ℕ} {StackSym State : Type} {input : List Bool} {s : ℕ}

instance instFintypeStackOp [Fintype StackSym] : Fintype (StackOp StackSym) :=
  Fintype.ofEquiv (Unit ⊕ StackSym ⊕ Unit)
    { toFun
        | .inl () => .stay
        | .inr (.inl γ) => .push γ
        | .inr (.inr ()) => .pop
      invFun
        | .stay => .inl ()
        | .push γ => .inr (.inl γ)
        | .pop => .inr (.inr ())
      left_inv x := by rcases x with ⟨⟩ | γ | ⟨⟩ <;> rfl
      right_inv x := by cases x <;> rfl }

instance instFintypeTuringAction [Fintype State] :
    Fintype (Turing.Action k Bool State) :=
  Fintype.ofEquiv _
    (Turing.MultiTapeNTM.ConfigurationGraph.actionEquiv (k := k) (State := State)).symm

instance instFintypeAuxPDAAction [Fintype StackSym] [Fintype State] :
    Fintype (AuxPDA.Action k Bool StackSym State) :=
  Fintype.ofEquiv (Turing.Action k Bool State × StackOp StackSym)
    { toFun
        | (t, op) => ⟨t, op⟩
      invFun a := (a.tape, a.stackOp)
      left_inv
        | (_, _) => rfl
      right_inv a := by cases a; rfl }

instance instDecidableEqTuringAction [DecidableEq State] :
    DecidableEq (Turing.Action k Bool State) :=
  letI : DecidableEq (Fin k → Option (Option Bool) × SignType) := inferInstance
  Equiv.decidableEq (Turing.MultiTapeNTM.ConfigurationGraph.actionEquiv (k := k) (State := State))

instance instDecidableEqAuxPDAAction [DecidableEq StackSym] [DecidableEq State] :
    DecidableEq (AuxPDA.Action k Bool StackSym State) := fun a b =>
  decidable_of_iff (a.tape = b.tape ∧ a.stackOp = b.stackOp)
    ⟨fun ⟨h1, h2⟩ => by cases a; cases b; cases h1; cases h2; rfl,
     fun h => by subst h; exact ⟨rfl, rfl⟩⟩

/-- `withEmptyStackHalt.Tr` is decidable whenever `M.Tr` is decidable over finite `StackSym` and
`State`. -/
instance instDecidableWithEmptyStackHaltTr [Fintype StackSym] [Fintype State]
    [DecidableEq StackSym] [DecidableEq State]
    {M : AuxPDA k Bool StackSym State}
    [∀ q inp work top act, Decidable (M.Tr q inp work top act)]
    (q : Option State) (inp : Option Bool) (work : Fin k → Option Bool)
    (top : Option StackSym) (act : AuxPDA.Action k Bool StackSym (Option State)) :
    Decidable (M.withEmptyStackHalt.Tr q inp work top act) := by
  cases q with
  | some q' =>
    dsimp only [withEmptyStackHalt]
    exact Fintype.decidableExistsFintype
  | none =>
    dsimp only [withEmptyStackHalt]
    infer_instance

lemma boundedStayStep_iff {M : AuxPDA k Bool StackSym State}
    {u v : BoundedSurfaceCfg k StackSym State input s} :
    M.BoundedStayStep u v ↔
      (u.state = none ∧ v = u) ∨
        ∃ q act, u.state = some q ∧
          M.Tr q u.inputSymbol u.workTapeSymbols u.topSym act ∧
          act.stackOp = .stay ∧
          applyBoundedTapes? act.tape u u.topSym = some v := by
  unfold BoundedStayStep StayStep
  constructor
  · rintro (⟨hhalt, heq⟩ | ⟨q, act, hq, htr, hop, heq⟩)
    · exact .inl ⟨hhalt, BoundedSurfaceCfg.toSurface_injective heq⟩
    · refine .inr ⟨q, act, hq, ?_, hop,
        (applyBoundedTapes?_eq_some_iff act.tape u v u.topSym).mpr heq⟩
      rwa [u.workTapeSymbols_eq_toSurface]
  · rintro (⟨hhalt, rfl⟩ | ⟨q, act, hq, htr, hop, happ⟩)
    · exact .inl ⟨hhalt, rfl⟩
    · refine .inr ⟨q, act, hq, ?_, hop,
        (applyBoundedTapes?_eq_some_iff act.tape u v u.topSym).mp happ⟩
      rwa [← u.workTapeSymbols_eq_toSurface]

lemma boundedPushStep_iff {M : AuxPDA k Bool StackSym State}
    {u v : BoundedSurfaceCfg k StackSym State input s} {γ : StackSym} :
    M.BoundedPushStep u γ v ↔
      ∃ q act, u.state = some q ∧
        M.Tr q u.inputSymbol u.workTapeSymbols u.topSym act ∧
        act.stackOp = .push γ ∧
        applyBoundedTapes? act.tape u (some γ) = some v := by
  unfold BoundedPushStep PushStep
  constructor
  · rintro ⟨q, act, hq, htr, hop, heq⟩
    refine ⟨q, act, hq, ?_, hop, (applyBoundedTapes?_eq_some_iff act.tape u v (some γ)).mpr heq⟩
    rwa [u.workTapeSymbols_eq_toSurface]
  · rintro ⟨q, act, hq, htr, hop, happ⟩
    refine ⟨q, act, hq, ?_, hop, (applyBoundedTapes?_eq_some_iff act.tape u v (some γ)).mp happ⟩
    rwa [← u.workTapeSymbols_eq_toSurface]

lemma boundedPopStep_iff {M : AuxPDA k Bool StackSym State}
    {u v : BoundedSurfaceCfg k StackSym State input s} {γ : StackSym} {baseTop : Option StackSym} :
    M.BoundedPopStep u γ baseTop v ↔
      u.topSym = some γ ∧
        ∃ q act, u.state = some q ∧
          M.Tr q u.inputSymbol u.workTapeSymbols (some γ) act ∧
          act.stackOp = .pop ∧
          applyBoundedTapes? act.tape u baseTop = some v := by
  unfold BoundedPopStep PopStep
  constructor
  · rintro ⟨htop, q, act, hq, htr, hop, heq⟩
    refine ⟨htop, q, act, hq, ?_, hop,
      (applyBoundedTapes?_eq_some_iff act.tape u v baseTop).mpr heq⟩
    rwa [u.workTapeSymbols_eq_toSurface]
  · rintro ⟨htop, q, act, hq, htr, hop, happ⟩
    refine ⟨htop, q, act, hq, ?_, hop,
      (applyBoundedTapes?_eq_some_iff act.tape u v baseTop).mp happ⟩
    rwa [← u.workTapeSymbols_eq_toSurface]

instance instDecidableBoundedStayStep [Fintype StackSym] [Fintype State]
    [DecidableEq StackSym] [DecidableEq State]
    {M : AuxPDA k Bool StackSym State}
    [∀ q inp work top act, Decidable (M.Tr q inp work top act)]
    (u v : BoundedSurfaceCfg k StackSym State input s) :
    Decidable (M.BoundedStayStep u v) :=
  decidable_of_iff' _ boundedStayStep_iff

instance instDecidableBoundedPushStep [Fintype StackSym] [Fintype State]
    [DecidableEq StackSym] [DecidableEq State]
    {M : AuxPDA k Bool StackSym State}
    [∀ q inp work top act, Decidable (M.Tr q inp work top act)]
    (u : BoundedSurfaceCfg k StackSym State input s) (γ : StackSym)
    (v : BoundedSurfaceCfg k StackSym State input s) :
    Decidable (M.BoundedPushStep u γ v) :=
  decidable_of_iff' _ boundedPushStep_iff

instance instDecidableBoundedPopStep [Fintype StackSym] [Fintype State]
    [DecidableEq StackSym] [DecidableEq State]
    {M : AuxPDA k Bool StackSym State}
    [∀ q inp work top act, Decidable (M.Tr q inp work top act)]
    (u : BoundedSurfaceCfg k StackSym State input s) (γ : StackSym) (baseTop : Option StackSym)
    (v : BoundedSurfaceCfg k StackSym State input s) :
    Decidable (M.BoundedPopStep u γ baseTop v) :=
  decidable_of_iff' _ boundedPopStep_iff

instance instDecidableBoundedPushPopStep [Fintype StackSym] [Fintype State]
    [DecidableEq StackSym] [DecidableEq State]
    {M : AuxPDA k Bool StackSym State}
    [∀ q inp work top act, Decidable (M.Tr q inp work top act)]
    (u u' v' v : BoundedSurfaceCfg k StackSym State input s) :
    Decidable (M.BoundedPushPopStep u u' v' v) :=
  Fintype.decidableExistsFintype

end DecidableTransitions

end Turing.AuxPDA
