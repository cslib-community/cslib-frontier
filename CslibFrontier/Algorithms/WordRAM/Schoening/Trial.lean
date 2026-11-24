/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.MemoryView
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.Schoening.Scan
public import CslibFrontier.Computability.WordRAM.Randomized.SampleBits

/-!
# One trial of Schöning's algorithm on the randomized word RAM

`Cslib.Algorithms.WordRAM.Schoening.trialProgram` is one trial of Schöning's k-SAT algorithm
[Schöning][Schoening1999] as a program of the randomized word RAM (`Cslib.WordRAM.runRand`). On the
input `encode φ`, the number `n` of variables followed by the clauses of `φ : CNF (Fin n)`, it

1. draws a uniformly random assignment, one `rand` call per variable;
2. performs `3 n` steps of local search: each step scans for the first falsified clause and, if
   there is one, flips the variable of a uniformly chosen literal occurrence of it;
3. halts with output `1` if the final assignment satisfies `φ` and `0` otherwise, leaving the
   final assignment in memory just after the input.

`Cslib.Algorithms.WordRAM.Schoening.trialProgram_spec` proves that the program halts on every path
within `trialTime n L = 36 n L + 66 n + 12 L + 19` instructions, where `L` is the input length,
makes at most `4 n` `rand` calls, reports correctly whether the assignment it leaves satisfies `φ`,
and that the law of that assignment is exactly the mathematical trial
`Cslib.Complexity.Schoening.trial φ`. Schöning's success bound for that trial
(`Cslib.Complexity.Schoening.trial_success_of_length_le`) therefore applies to the program. Time is
the instruction count of the word RAM with unit-cost `rand` (`Cslib.WordRAM.stepRand`); every
instruction counts, including loop tests and jumps.

The trial body `Cslib.Algorithms.WordRAM.Schoening.trialCore` reads the clause region and the
number of variables from registers, so the amplified algorithm reuses it with a different input
layout. It writes memory only in the assignment: `Cslib.Algorithms.WordRAM.Schoening.Frame` records
that the memory after the assignment is unchanged, which is where the amplified algorithm keeps its
trial counter.

## Main definitions

* `Cslib.Algorithms.WordRAM.Schoening.Frame`: the registers and memory a trial relies on.
* `Cslib.Algorithms.WordRAM.Schoening.initAssign`, `Cslib.Algorithms.WordRAM.Schoening.flip`,
  `Cslib.Algorithms.WordRAM.Schoening.stepBody`, `Cslib.Algorithms.WordRAM.Schoening.walkLoop`,
  `Cslib.Algorithms.WordRAM.Schoening.trialCore`: the parts of a trial.
* `Cslib.Algorithms.WordRAM.Schoening.trialCode`, `Cslib.Algorithms.WordRAM.Schoening.trialProgram`:
  a trial on the input `encode φ`, structured and compiled.
* `Cslib.Algorithms.WordRAM.Schoening.trialTime`: its instruction bound.
* `Cslib.Algorithms.WordRAM.Schoening.cfgAssignment`: the assignment left by a halting run.

## Main results

* `Cslib.Algorithms.WordRAM.Schoening.trialCore_law`: the trial body has the law of
  `Cslib.Complexity.Schoening.trial`.
* `Cslib.Algorithms.WordRAM.Schoening.trialProgram_spec`: halting, time and `rand` bounds, a
  correct output, and the exact law of the trial for the compiled program.

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Schoening

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.Schoening Cslib.BitString
open Reg

variable {n : ℕ}

/-! ### Reading assignments -/

/-- The assignment left by a halting run: read from address `base`. -/
def cfgAssignment {r : ℕ} (base n : ℕ) : RandCfg r → (Fin n → Bool)
  | .halted _ d => assignmentAt d.mem base n
  | _ => fun _ => false

/-- `AssignAt` for the assignment read back from bits. -/
theorem assignAt_assignmentAt {mem : ℕ → ℕ} {base : ℕ} (h : ∀ i < n, mem (base + i) ≤ 1) :
    AssignAt mem base (assignmentAt mem base n) := by
  intro i
  have := h i i.isLt
  simp only [assignmentAt]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h0 | h1 <;> simp [*]

/-- The `found` word reported by a clause scan is `0` when `σ` satisfies `φ` and `1` otherwise. -/
theorem ScanResult.found_eq {σ : Fin n → Bool} {φ : CNF (Fin n)} {mem : ℕ → ℕ} {e fnd cptr : ℕ}
    (h : ScanResult σ φ mem e fnd cptr) :
    fnd = if φ.eval σ then 0 else 1 := by
  unfold ScanResult at h
  rcases hfu : firstUnsat φ σ with _ | c <;> simp only [hfu] at h
  · simp [h, (firstUnsat_eq_none_iff _ _).mp hfu]
  · have : φ.eval σ = false := by
      rcases he : φ.eval σ
      · rfl
      · rw [← firstUnsat_eq_none_iff] at he; rw [he] at hfu; cases hfu
    rw [h.1, this]
    rfl

/-- On the initial machine data for `encode φ`, the encoded clauses start at address `2`. -/
theorem holdsList_encodeClauses_init {r : ℕ} (φ : CNF (Fin n)) :
    HoldsList 2 (encodeClauses φ) (Data.init (encode φ) : Data r).mem := fun i => by
  change (Data.init (encode φ) : Data r).mem (2 + i.val) = (encodeClauses φ)[i.val]
  rw [show 2 + i.val = (1 + i.val) + 1 by omega, Data.init_mem_succ]
  simp [encode, Nat.add_comm 1 i.val]

/-! ### The frame of a trial -/

/-- The registers and memory a trial relies on: the constants, the clauses of `φ` stored in
`[C, A)`, the assignment's address `A`, and `n`. The memory from address `A + n` on, just after
the assignment, agrees with `M`; a trial never writes there, so callers can keep data such as a
trial counter in it. -/
structure Frame (φ : CNF (Fin n)) (C A : ℕ) (M : ℕ → ℕ) (x : Data 24) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  cBeg_eq : x.regs cBeg = C
  aBase_eq : x.regs aBase = A
  nReg_eq : x.regs nReg = n
  clauses : HoldsList C (encodeClauses φ) x.mem
  span : C + (encodeClauses φ).length = A
  rest : ∀ a, A + n ≤ a → x.mem a = M a

/-- The frame survives any change that keeps its registers and the memory outside the assignment
`[A, A + n)`. -/
theorem Frame.congr {φ : CNF (Fin n)} {C A : ℕ} {M : ℕ → ℕ} {x y : Data 24}
    (h : Frame φ C A M x) (hz : y.regs zero = x.regs zero) (ho : y.regs one = x.regs one)
    (hc : y.regs cBeg = x.regs cBeg) (ha : y.regs aBase = x.regs aBase)
    (hn : y.regs nReg = x.regs nReg) (hmem : ∀ a, a < A ∨ A + n ≤ a → y.mem a = x.mem a) :
    Frame φ C A M y := by
  struct_frame h

/-- The frame with the memory after the assignment taken as it is. -/
theorem Frame.self {φ : CNF (Fin n)} {C A : ℕ} {M : ℕ → ℕ} {x : Data 24} (h : Frame φ C A M x) :
    Frame φ C A x.mem x :=
  { h with rest := fun _ _ => rfl }

/-- The frame survives any change that keeps its registers and the memory below `A`, with the
memory after the assignment taken as it is. -/
theorem Frame.of_mem_lt {φ : CNF (Fin n)} {C A : ℕ} {M : ℕ → ℕ} {x y : Data 24}
    (h : Frame φ C A M x) (hz : y.regs zero = x.regs zero) (ho : y.regs one = x.regs one)
    (hc : y.regs cBeg = x.regs cBeg) (ha : y.regs aBase = x.regs aBase)
    (hn : y.regs nReg = x.regs nReg) (hmem : ∀ a < A, y.mem a = x.mem a) :
    Frame φ C A y.mem y := by
  struct_frame h

/-- Code that writes none of the frame registers keeps the frame registers. -/
def PreservesFrame (c : Code .standard 24) : Prop :=
  c.Preserves zero ∧ c.Preserves one ∧ c.Preserves cBeg ∧ c.Preserves aBase ∧ c.Preserves nReg

instance (c : Code .standard 24) : Decidable (PreservesFrame c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A deterministic run of frame-preserving code that keeps the memory outside the assignment
keeps the frame. -/
theorem Frame.of_execWithin {φ : CNF (Fin n)} {C A : ℕ} {M : ℕ → ℕ} {c : Code .standard 24}
    {x y : Data 24} {w T : ℕ} (h : Frame φ C A M x) (hc : PreservesFrame c)
    (he : ExecWithin w c x y T) (hmem : ∀ a, a < A ∨ A + n ≤ a → y.mem a = x.mem a) :
    Frame φ C A M y :=
  h.congr (he.regs_eq hc.1) (he.regs_eq hc.2.1) (he.regs_eq hc.2.2.1) (he.regs_eq hc.2.2.2.1)
    (he.regs_eq hc.2.2.2.2) hmem

/-- The frame after setting a register outside it. -/
private theorem Frame.set {φ : CNF (Fin n)} {C A : ℕ} {M : ℕ → ℕ} {x : Data 24}
    (h : Frame φ C A M x) {i : Fin 24}
    (hi : i ∉ ({zero, one, cBeg, aBase, nReg} : Finset (Fin 24))) (v : ℕ) :
    Frame φ C A M (x.set i v) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  obtain ⟨_, _, _, _, _⟩ := hi
  struct_frame h

/-! ### The random initial assignment -/

/-- **The random initial assignment**: draw all `n` variables via `Cslib.WordRAM.sampleBits`. -/
def initAssign : Code .standard 24 :=
  sampleBits zero one aBase nReg cnt val addr

/-- **The random initial assignment** is uniform, takes `6 n + 3` instructions and `n` `rand`
calls, and keeps the frame. -/
theorem initAssign_law {φ : CNF (Fin n)} {C A w : ℕ} {M : ℕ → ℕ}
    (hw : Fits w (A + 3 * n)) (hA : 1 ≤ A)
    {x : Data 24} (hx : Frame φ C A M x) :
    ExecRandLaw w initAssign x (fun y => Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1)
      (6 * n + 3) n (fun y => assignmentAt y.mem A n)
      (Probability.PMF.uniformOfFintype (Fin n → Bool)) := by
  have h := sampleBits_law (r := 24) (w := w) (base := A) (n := n)
    (zero := zero) (one := one) (baseReg := aBase) (nReg := nReg)
    (cnt := cnt) (val := val) (addr := addr) (by decide)
    (hw.of_le (by omega)) (hw.of_le (by omega))
    hx.zero_eq hx.one_eq hx.aBase_eq hx.nReg_eq
  exact h.mono (fun y ⟨hyb, hym, hyr⟩ =>
    ⟨hx.congr (hyr zero (by decide) (by decide) (by decide))
      (hyr one (by decide) (by decide) (by decide))
      (hyr cBeg (by decide) (by decide) (by decide))
      (hyr aBase (by decide) (by decide) (by decide))
      (hyr nReg (by decide) (by decide) (by decide))
      (fun a ha => hym a (by omega)),
     hyb⟩) le_rfl le_rfl

/-! ### Flipping a literal of a falsified clause -/

/-- Read the literal at offset `var` of the clause at `cPtr` and flip its variable. -/
def flipRest : Code .standard 24 := ram[
  addr ← cPtr + one; addr ← addr + var; lit ← *addr; var ← lit >>> one; addr ← aBase + var;
  val ← *addr; val ← one - val; *addr ← val ]

/-- **One flip**: choose a literal occurrence of the clause at `cPtr` uniformly and flip its
variable; an empty clause changes nothing. -/
def flip : Code .standard 24 := ram[
  len ← *cPtr;
  if zero < len then [ len ← len - one; var ← rand len; ⟪flipRest⟫ ] else [ len ← len ] ]

/-- **One flip** has the law of `Cslib.Complexity.Schoening.flipStep`. -/
theorem flip_law {φ : CNF (Fin n)} {C A w : ℕ} {M : ℕ → ℕ} (hw : Fits w (A + 3 * n)) {x : Data 24}
    (hx : Frame φ C A M x) {σ : Fin n → Bool} (hσ : AssignAt x.mem A σ) {c : Clause (Fin n)}
    (hcl : HoldsList (x.regs cPtr) (encodeClause c) x.mem) (hend : x.regs cPtr + c.length + 1 ≤ A) :
    ExecRandLaw w flip x (fun y => Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1) 12 1
      (fun y => assignmentAt y.mem A n) (flipStep c σ) := by
  have hlen : x.mem (x.regs cPtr) = c.length := by simpa [encodeClause_eq] using hcl.get 0 (by simp)
  have hbits : ∀ i < n, x.mem (A + i) ≤ 1 := fun i hi => by
    rw [show A + i = A + (⟨i, hi⟩ : Fin n).val from rfl, hσ]; cases σ ⟨i, hi⟩ <;> decide
  have hload := ExecWithin.load (B := .standard) (w := w) (d := len) (a := cPtr) (x := x)
  rw [hlen] at hload
  have hx₁ : Frame φ C A M (x.set len c.length) := hx.set (by decide) _
  rcases hℓ : c.length with _ | ℓ
  · -- an empty clause: nothing changes
    have hc : ¬(Cond.lt zero len).Holds (x.set len c.length) := by
      simp +decide [Cond.holds_lt, hℓ]
    have hneg := ExecRandLaw.branch_neg (pos := ram[ len ← len - one; var ← rand len; ⟪flipRest⟫ ])
      hc (ExecRandLaw.of_execWithin (f := fun y => assignmentAt y.mem A n)
        (P := fun y => Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1)
        (ExecWithin.copy (B := .standard) (w := w) (d := len) (s := len)
          (x := x.set len c.length))
        ⟨hx₁.set (by decide) _, by simpa using hbits⟩)
    rw [hℓ] at hload
    refine ((ExecRandLaw.seq_det hload (by rw [← hℓ]; exact hneg)).congr_law ?_).mono
      (fun _ h => h) (by omega) (by omega)
    simp only [Data.set_mem, assignmentAt_eq hσ, flipStep, hℓ, ↓reduceDIte]
  · -- a nonempty clause: a uniform literal occurrence
    have hc : (Cond.lt zero len).Holds (x.set len c.length) := by
      simp +decide [Cond.holds_lt, hℓ, hx.zero_eq]
    have hf0 : Fits w ℓ := hw.of_le (by omega)
    let F : ℕ → (Fin n → Bool) := fun k =>
      if hk : k < c.length then flipOn {(c.get ⟨k, hk⟩).1} σ else σ
    let x₂ := (x.set len c.length).set len ℓ
    have hx₂len : x₂.regs len = ℓ := by wram_simp [x₂]
    have hsub : ExecWithin w (ram[ len ← len - one ]) (x.set len c.length) x₂ 1 :=
      WP.execWithin (by wram_exec [hx.one_eq, hℓ, Nat.add_sub_cancel]; rfl)
    -- the deterministic rest after drawing `k`
    have hrest : ∀ k : Fin (x₂.regs len + 1), ∃ y, ExecWithin w flipRest (x₂.set var k.val) y 8 ∧
        (Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1) ∧ assignmentAt y.mem A n = F k.val := by
      intro k
      have hk : k.val < c.length := by have := k.isLt; have := hx₂len; omega
      set l := c.get ⟨k.val, hk⟩ with hl
      have hlv : l.1.val < n := l.1.isLt
      have hlit : x.mem (x.regs cPtr + 1 + k.val) = litCode l := by
        have h := hcl.get (k.val + 1) (by simp; omega)
        simp only [encodeClause_eq, List.getElem_cons_succ, List.getElem_map] at h
        rw [show x.regs cPtr + 1 + k.val = x.regs cPtr + (k.val + 1) by omega, h, hl,
          List.get_eq_getElem]
      have : Fits w (x.regs cPtr + 1) := hw.of_le (by omega)
      have : Fits w (x.regs cPtr + 1 + k.val) := hw.of_le (by omega)
      have : Fits w l.1.val := hw.of_le (by omega)
      have : Fits w (A + l.1.val) := hw.of_le (by omega)
      have : Fits w (1 - (σ l.1).toNat) := hw.of_le (by omega)
      refine WP.exists_execWithin ?_
      unfold flipRest
      wram_exec [x₂, hx.one_eq, hx.aBase_eq, hlit, litCode_shiftRight, hσ l.1]
      refine ⟨⟨by dsimp only [x₂]; struct_frame hx, fun i hi => ?_⟩, ?_⟩
      · dsimp only [x₂]
        simp only [Data.set_mem, Data.write_mem, Function.update_apply]
        split_ifs
        · omega
        · exact hbits i hi
      · dsimp only [x₂]
        simp only [Data.set_mem, Data.write_mem,
          show assignmentAt (Function.update x.mem (A + l.1.val) (1 - (σ l.1).toNat)) A n =
              Function.update (assignmentAt x.mem A n) l.1 (decide (1 - (σ l.1).toNat = 1)) from
            bitsAt_update_self x.mem A l.1 (1 - (σ l.1).toNat),
          assignmentAt_eq hσ, F, hk, ↓reduceDIte, ← hl]
        funext i
        rw [flipOn_apply, Function.update_apply]
        by_cases hi : i = l.1
        · subst hi; cases σ l.1 <;> simp
        · simp [hi]
    choose y hy hpost hlaw using hrest
    have hrand := ExecRandLaw.rand_seq (w := w) (f := fun y => assignmentAt y.mem A n)
      (P := fun y => Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1) (dst := var) (src := len)
      (x := x₂) (y := y) (by rw [hx₂len]; exact hf0) hy hpost
    have hpos := ExecRandLaw.branch_pos (neg := ram[ len ← len ]) hc
      (ExecRandLaw.seq_det hsub hrand)
    refine ((ExecRandLaw.seq_det hload hpos).congr_law ?_).mono (fun _ h => h) (by omega) le_rfl
    rw [show (fun k : Fin (x₂.regs len + 1) => assignmentAt (y k).mem A n) =
        fun k => F k.val from funext hlaw, hx₂len]
    have hne : c.length ≠ 0 := by omega
    have : NeZero c.length := ⟨hne⟩
    simp only [flipStep, hne, ↓reduceDIte]
    rw [← Probability.PMF.uniformOfFintype_map_equiv (finCongr hℓ), PMF.map_comp]
    congr 1 with i : 1
    simp [F, i.isLt]

/-! ### One step of local search -/

/-- **One step**: scan for the first falsified clause and flip a literal of it, then count the
step. -/
def stepBody : Code .standard 24 := ram[
  ⟪scan⟫; if found = one then [ ⟪flip⟫ ] else [ found ← found ]; cnt ← cnt + one ]

/-- The law of one step of `Cslib.Complexity.Schoening.walk`. -/
noncomputable def stepLaw (φ : CNF (Fin n)) (σ : Fin n → Bool) : PMF (Fin n → Bool) :=
  match firstUnsat φ σ with
  | none => PMF.pure σ
  | some c => flipStep c σ

/-- A satisfying assignment is never moved. -/
theorem walk_of_firstUnsat_none {φ : CNF (Fin n)} {σ : Fin n → Bool} (h : firstUnsat φ σ = none)
    (t : ℕ) : walk φ t σ = PMF.pure σ := by
  cases t with
  | zero => rfl
  | succ t => simp only [walk, h]

/-- One more step of the walk is a step followed by the walk. -/
theorem walk_succ_eq_bind (φ : CNF (Fin n)) (t : ℕ) (σ : Fin n → Bool) :
    walk φ (t + 1) σ = (stepLaw φ σ).bind (walk φ t) := by
  rcases h : firstUnsat φ σ with _ | c
  · simp only [walk, stepLaw, h, PMF.pure_bind, walk_of_firstUnsat_none h]
  · simp only [walk, stepLaw, h]

/-- **One step** has the law `stepLaw φ σ`, within `12 E + 18` instructions and one `rand`
call. -/
theorem stepBody_law {φ : CNF (Fin n)} {C A w : ℕ} {M : ℕ → ℕ}
    (hw : Fits w (A + 3 * n)) (hA : 1 ≤ A)
    {x : Data 24} (hx : Frame φ C A M x) (hbits : ∀ i < n, x.mem (A + i) ≤ 1)
    (hcnt : Fits w (x.regs cnt + 1)) :
    ExecRandLaw w stepBody x
      (fun y => (Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1) ∧ y.regs cnt = x.regs cnt + 1 ∧
        y.regs steps = x.regs steps)
      (12 * (encodeClauses φ).length + 18) 1 (fun y => assignmentAt y.mem A n)
      (stepLaw φ (assignmentAt x.mem A n)) := by
  set σ := assignmentAt x.mem A n with hσdef
  have hσ : AssignAt x.mem A σ := assignAt_assignmentAt hbits
  obtain ⟨y₁, hy₁, hm₁, hr₁⟩ := scan_spec (w := w) σ φ x hx.zero_eq hx.one_eq
    (by rw [hx.cBeg_eq]; exact hx.clauses) (by rw [hx.cBeg_eq, hx.aBase_eq]; exact hx.span)
    (by rw [hx.aBase_eq]; exact hσ) (by rw [hx.aBase_eq]; exact hw.of_le (by omega))
    (by rw [hx.aBase_eq]; omega)
  have hpf : PreservesFrame scan := by decide
  have hx₁ : Frame φ C A M y₁ := hx.of_execWithin hpf hy₁ fun a _ => by rw [hm₁]
  have hc₁ : y₁.regs cnt = x.regs cnt := hy₁.regs_eq (by decide)
  have hs₁ : y₁.regs steps = x.regs steps := hy₁.regs_eq (by decide)
  rw [hx.aBase_eq] at hr₁
  have hinc (z : Data 24) (hz1 : z.regs one = 1) (hzc : z.regs cnt = x.regs cnt) :
      ExecWithin w (ram[ cnt ← cnt + one ]) z (z.set cnt (x.regs cnt + 1)) 1 :=
    WP.execWithin (by wram_exec [hz1, hzc]; rfl)
  unfold ScanResult at hr₁
  rcases hfu : firstUnsat φ σ with _ | c
  · -- no falsified clause: nothing to flip
    simp only [hfu] at hr₁
    have hc : ¬(Cond.eq found one).Holds y₁ := by simp [Cond.holds_eq, hr₁, hx₁.one_eq]
    have hrun := hy₁.seq ((ExecWithin.branch_neg (pos := flip) hc
      (ExecWithin.copy (B := .standard) (w := w) (d := found) (s := found) (x := y₁))).seq
      (hinc _ (by simpa +decide using hx₁.one_eq) (by simpa +decide using hc₁)))
    have h := ExecRandLaw.of_execWithin (f := fun y => assignmentAt y.mem A n)
      (P := fun y => (Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1) ∧
        y.regs cnt = x.regs cnt + 1 ∧ y.regs steps = x.regs steps) hrun
      ⟨⟨(hx₁.set (by decide) _).set (by decide) _, by simpa [hm₁] using hbits⟩,
        by simp, by simpa +decide using hs₁⟩
    refine (h.congr_law ?_).mono (fun _ h => h) (by omega) (by omega)
    simp only [stepLaw, hfu, Data.set_mem, hm₁]
    rfl
  · -- flip a literal of the first falsified clause
    simp only [hfu] at hr₁
    obtain ⟨hf, hcl, hend⟩ := hr₁
    have hc : (Cond.eq found one).Holds y₁ := by simp [Cond.holds_eq, hf, hx₁.one_eq]
    have hflip := flip_law (φ := φ) (C := C) hw hx₁ (σ := σ) (by rw [hm₁]; exact hσ)
      (by rw [hm₁]; exact hcl) hend
    have hflip' := (((hflip.withPreserves (i := cnt) (by decide)).withPreserves (i := steps)
      (by decide)).withPreserves (i := one) (by decide))
    have hb := ExecRandLaw.branch_pos (neg := ram[ found ← found ]) hc hflip'
    have hstep := ExecRandLaw.seq_det hy₁ (ExecRandLaw.seq_det_right
      (Q := fun y => (Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1) ∧
        y.regs cnt = x.regs cnt + 1 ∧ y.regs steps = x.regs steps) (T₂ := 1) hb
      fun z ⟨⟨⟨⟨hz, hzb⟩, hzc⟩, hzs⟩, hzo⟩ =>
        ⟨_, hinc z (by rw [hzo, hx₁.one_eq]) (by rw [hzc, hc₁]),
          ⟨⟨hz.set (by decide) _, by simpa using hzb⟩, by simp,
            by simpa +decide [hs₁] using hzs⟩, by simp⟩)
    refine (hstep.congr_law ?_).mono (fun _ h => h) (by omega) le_rfl
    simp [stepLaw, hfu]

/-! ### The local search -/

/-- **The local search**: steps `cnt, …, steps - 1`. -/
def walkLoop : Code .standard 24 := .loop (.lt cnt steps) stepBody

/-- **The local search** from `t` remaining steps has the law of `walk φ t`. -/
theorem walkLoop_law {φ : CNF (Fin n)} {C A w : ℕ} {M : ℕ → ℕ}
    (hw : Fits w (A + 3 * n)) (hA : 1 ≤ A) :
    ∀ (t : ℕ) (x : Data 24), Frame φ C A M x → (∀ i < n, x.mem (A + i) ≤ 1) →
      x.regs cnt + t = x.regs steps → Fits w (x.regs steps) →
      ExecRandLaw w walkLoop x (fun y => Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1)
        (t * (12 * (encodeClauses φ).length + 20) + 2) t (fun y => assignmentAt y.mem A n)
        (walk φ t (assignmentAt x.mem A n))
  | 0, x, hx, hbits, ht, _ => by
    have hc : ¬(Cond.lt cnt steps).Holds x := by simp [Cond.holds_lt, ← ht]
    exact (ExecRandLaw.loop_exit hc ⟨hx, hbits⟩).mono (fun _ h => h) (by omega) le_rfl
  | t + 1, x, hx, hbits, ht, hfs => by
    have hc : (Cond.lt cnt steps).Holds x := by simp [Cond.holds_lt, ← ht]
    have hb := stepBody_law (φ := φ) hw hA hx hbits (hfs.of_le (by omega))
    have h := ExecRandLaw.loop_iter (κ := walk φ t) hc hb fun y ⟨⟨hy, hyb⟩, hyc, hys⟩ =>
      walkLoop_law hw hA t y hy hyb (by omega) (by rw [hys]; exact hfs)
    rw [walk_succ_eq_bind]
    have := Nat.add_mul t 1 (12 * (encodeClauses φ).length + 20)
    exact h.mono (fun _ h => h) (by omega) (by omega)

/-! ### One trial -/

/-- **The body of a trial**: a uniform assignment, `3 n` steps of local search, and the final
check, which sets `out` to `1` exactly when the assignment satisfies the formula. The clauses are
read from `[cBeg, aBase)`, the assignment is stored from `aBase`, and `n` is read from `nReg`. -/
def trialCore : Code .standard 24 := ram[
  ⟪initAssign⟫; ⟪ram[ steps ← nReg + nReg; steps ← steps + nReg; cnt ← zero ]⟫; ⟪walkLoop⟫;
  ⟪ram[ ⟪scan⟫; out ← one - found ]⟫ ]

/-- The instruction bound of a trial body on `n` variables and a clause encoding of length
`E`. -/
def trialCoreTime (n E : ℕ) : ℕ := 36 * n * E + 66 * n + 12 * E + 13

/-- **The body of a trial** has the law of `Cslib.Complexity.Schoening.trial`, keeps the frame,
and sets `out` to whether the assignment it leaves satisfies the formula. -/
theorem trialCore_law {φ : CNF (Fin n)} {C A w : ℕ} {M : ℕ → ℕ}
    (hw : Fits w (A + 3 * n)) (hA : 1 ≤ A)
    {x : Data 24} (hx : Frame φ C A M x) :
    ExecRandLaw w trialCore x
      (fun y => (Frame φ C A M y ∧ ∀ i < n, y.mem (A + i) ≤ 1) ∧
        y.regs out = if φ.eval (assignmentAt y.mem A n) then 1 else 0)
      (trialCoreTime n (encodeClauses φ).length) (4 * n) (fun y => assignmentAt y.mem A n)
      (trial φ) := by
  have hinit := initAssign_law (φ := φ) hw hA hx
  have h := ExecRandLaw.seq (κ := walk φ (3 * n)) (R₂ := 3 * n)
    (T₂ := 3 + (3 * n * (12 * (encodeClauses φ).length + 20) + 2 +
      (12 * (encodeClauses φ).length + 5))) hinit fun y ⟨hy, hyb⟩ => by
    have hf2 : Fits w (n + n) := hw.of_le (by omega)
    have hf3 : Fits w (n + n + n) := hw.of_le (by omega)
    let y₃ := ((y.set steps (n + n)).set steps (n + n + n)).set cnt 0
    have hpre : ExecWithin w (ram[ steps ← nReg + nReg; steps ← steps + nReg; cnt ← zero ]) y y₃
        3 := WP.execWithin (by wram_exec [hy.nReg_eq, hy.zero_eq]; rfl)
    have hy₃ : Frame φ C A M y₃ := ((hy.set (by decide) _).set (by decide) _).set (by decide) _
    have hwalk := walkLoop_law (φ := φ) hw hA (3 * n) y₃ hy₃ (by simpa [y₃] using hyb)
      (by wram_simp [y₃]; omega) (by wram_simp [y₃]; exact hf3)
    have hpost : ∀ z, (Frame φ C A M z ∧ ∀ i < n, z.mem (A + i) ≤ 1) →
        ∃ z', ExecWithin w (ram[ ⟪scan⟫; out ← one - found ]) z z'
          (12 * (encodeClauses φ).length + 5) ∧
          ((Frame φ C A M z' ∧ ∀ i < n, z'.mem (A + i) ≤ 1) ∧
            z'.regs out = if φ.eval (assignmentAt z'.mem A n) then 1 else 0) ∧
          assignmentAt z'.mem A n = assignmentAt z.mem A n := by
      intro z ⟨hz, hzb⟩
      obtain ⟨z₁, hz₁, hm₁, hr₁⟩ := scan_spec (w := w) (assignmentAt z.mem A n) φ z hz.zero_eq
        hz.one_eq (by rw [hz.cBeg_eq]; exact hz.clauses)
        (by rw [hz.cBeg_eq, hz.aBase_eq]; exact hz.span)
        (by rw [hz.aBase_eq]; exact assignAt_assignmentAt hzb)
        (by rw [hz.aBase_eq]; exact hw.of_le (by omega)) (by rw [hz.aBase_eq]; omega)
      have hzf₁ : Frame φ C A M z₁ := hz.of_execWithin (by decide) hz₁ fun a _ => by rw [hm₁]
      have : Fits w (1 - z₁.regs found) := hw.of_le (by omega)
      refine WP.exists_execWithin (WP.seq (WP.of_execWithin hz₁ ?_))
      wram_exec [hzf₁.one_eq, hr₁.found_eq]
      refine ⟨⟨⟨hzf₁.set (by decide) _, by simpa [hm₁] using hzb⟩, ?_⟩, by simp [hm₁]⟩
      wram_simp [hm₁]
      split_ifs <;> rfl
    have hrest := ExecRandLaw.seq_det hpre (ExecRandLaw.seq_det_right hwalk hpost)
    simpa [y₃] using hrest
  have hR : n + 3 * n ≤ 4 * n := by omega
  have hT : 6 * n + 3 + (3 + (3 * n * (12 * (encodeClauses φ).length + 20) + 2 +
      (12 * (encodeClauses φ).length + 5))) ≤ trialCoreTime n (encodeClauses φ).length := by
    simp only [trialCoreTime]
    ring_nf
    omega
  have hlaw : (Probability.PMF.uniformOfFintype (Fin n → Bool)).bind (walk φ (3 * n)) =
      trial φ := by
    simp only [trial, Fintype.card_fin]
  exact (h.congr_law hlaw).mono (fun _ h => h) hT hR

/-! ### The program -/

/-- Set up the registers of a trial on the input `encode φ`: the clauses start at address `2`,
and the assignment is stored just after the input. -/
def trialSetup : Code .standard 24 := ram[
  one ← #1; val ← *zero; aBase ← val + one; nReg ← *one; cBeg ← one + one ]

/-- **One trial of Schöning's algorithm** on the input `encode φ`, as a structured program. -/
def trialCode : Code .standard 24 := ram[ ⟪trialSetup⟫; ⟪trialCore⟫ ]

/-- **One trial of Schöning's algorithm** on the input `encode φ`, halting with `out`. -/
def trialProgram : Program .standard 24 := trialCode.program out

/-- The instruction bound of a trial on `n` variables and an input of length `L`. -/
def trialTime (n L : ℕ) : ℕ := 36 * n * L + 66 * n + 12 * L + 19

theorem length_encode (φ : CNF (Fin n)) : (encode φ).length = (encodeClauses φ).length + 1 := by
  simp [encode]

/-- The data after the setup of a trial on the input `encode φ`. -/
def setupData (φ : CNF (Fin n)) : Data 24 :=
  (((((Data.init (encode φ)).set one 1).set val (encode φ).length).set aBase
    ((encode φ).length + 1)).set nReg n).set cBeg 2

/-- The setup establishes the frame of a trial on the input `encode φ`. -/
theorem trialSetup_exec (φ : CNF (Fin n)) {w : ℕ} (hw : Fits w ((encode φ).length + 3 * n + 1)) :
    ExecWithin w trialSetup (Data.init (encode φ)) (setupData φ) 5 ∧
      Frame φ 2 ((encode φ).length + 1) (setupData φ).mem (setupData φ) := by
  have : Fits w 1 := hw.of_le (by omega)
  have : Fits w ((encode φ).length + 1) := hw.of_le (by omega)
  have : Fits w 2 := hw.of_le (by simp [encode]; omega)
  have hm0 : (Data.init (encode φ) : Data 24).mem 0 = (encode φ).length := rfl
  have hm1 : (Data.init (encode φ) : Data 24).mem 1 = n := rfl
  refine ⟨WP.execWithin (by
      unfold trialSetup setupData
      wram_exec [Data.init_regs, hm0, hm1]
      rfl), ?_⟩
  refine ⟨by wram_simp [setupData, Data.init_regs], by wram_simp [setupData],
    by wram_simp [setupData], by wram_simp [setupData], by wram_simp [setupData],
    holdsList_encodeClauses_init (r := 24) φ, by simp [length_encode]; omega, fun _ _ => rfl⟩

/-- **One trial of Schöning's algorithm on the randomized word RAM.** On the input `encode φ` of
length `L`, at any word size `w` with `L + 3 n + 1 < 2 ^ w`, the program

* halts on every path within `trialTime n L = 36 n L + 66 n + 12 L + 19` instructions;
* makes at most `4 n` `rand` calls;
* outputs `1` exactly when the assignment it leaves at address `L + 1` satisfies `φ`;
* leaves an assignment whose law is exactly `Cslib.Complexity.Schoening.trial φ`. -/
theorem trialProgram_spec (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((encode φ).length + 3 * n + 1)) :
    RandHaltsWithin w trialProgram (.init (encode φ)) (trialTime n (encode φ).length) ∧
    RandCallsBounded w trialProgram (.init (encode φ)) (trialTime n (encode φ).length) (4 * n) ∧
    (∀ cfg ∈ (runRand w trialProgram (trialTime n (encode φ).length)
        (.running (.init (encode φ)))).support,
      ∃ d : Data 24, cfg = .halted
        (if φ.eval (assignmentAt d.mem ((encode φ).length + 1) n) then 1 else 0) d) ∧
    (evalRand w trialProgram (trialTime n (encode φ).length) (.init (encode φ))).map
      (cfgAssignment ((encode φ).length + 1) n) = trial φ := by
  set A := (encode φ).length + 1
  obtain ⟨hy, hfr⟩ := trialSetup_exec φ hw
  have hA : 1 ≤ A := by omega
  have hw' : Fits w (A + 3 * n) := hw.of_le (by omega)
  have hcore := ExecRandLaw.seq_det hy (trialCore_law (φ := φ) hw' hA hfr)
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := hcore.program out (T' := trialTime n (encode φ).length)
    (by simp only [trialCoreTime, trialTime, length_encode]; nlinarith)
    (cfgAssignment A n) fun _ _ => rfl
  refine ⟨hhalt, hcalls, fun cfg hcfg => ?_, hlaw⟩
  obtain ⟨d, rfl, -, hd⟩ := hpost cfg hcfg
  exact ⟨d, by rw [hd]⟩

end Cslib.Algorithms.WordRAM.Schoening

end
