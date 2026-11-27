/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.CSP.VariableElimination
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
public import CslibFrontier.Computability.WordRAM.Realization.PrefixFrame
import CslibFrontier.Tactic.Realize

/-!
# Monotone Memory Predicates, `memScan`, and `writeDesc`

Factor descriptor invariants over allocated Word-RAM list blocks, together with the shared linear
membership scanner `memScan` and 4-word descriptor writer `writeDesc`.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.HoldsFactor`, `HoldsFactorList`, `AllDataBelow`:
  append-only memory layout predicates for factor descriptors.
* `Cslib.Algorithms.WordRAM.VariableElimination.memScan`: linear array membership scan.
* `Cslib.Algorithms.WordRAM.VariableElimination.writeDesc`: 4-word factor descriptor writer.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Factor descriptors -/

/-- A 4-word factor descriptor at `descAddr` points to `f`'s scope and entries. -/
@[expose] def HoldsFactor (descAddr : ℕ) (f : FactorTable ℕ ℕ) (s : Memory.State) : Prop :=
  descAddr + 4 ≤ s.frontier ∧
  s.mem (descAddr + 1) = f.scope.length ∧
  s.mem (descAddr + 3) = f.entries.size ∧
  HoldsIn (s.mem descAddr) f.scope s ∧
  HoldsIn (s.mem (descAddr + 2)) f.entries.toList s

theorem HoldsFactor.mono {descAddr : ℕ} {f : FactorTable ℕ ℕ} {F : ℕ}
    {s₀ s₁ : Memory.State} (h : HoldsFactor descAddr f s₀)
    (hF : descAddr + 4 ≤ F)
    (hsF : s₀.mem descAddr + f.scope.length ≤ F)
    (heF : s₀.mem (descAddr + 2) + f.entries.size ≤ F)
    (hp : PreservesBelow F s₀ s₁) : HoldsFactor descAddr f s₁ := by
  obtain ⟨hd, hsl, hel, hsc, hent⟩ := h
  unfold HoldsFactor
  rw [hp.2.2 descAddr (by omega), hp.2.2 (descAddr + 1) (by omega),
    hp.2.2 (descAddr + 2) (by omega), hp.2.2 (descAddr + 3) (by omega)]
  exact ⟨hd.trans hp.2.1, hsl, hel, hsc.mono hsF hp,
    hent.mono (by simpa [Array.length_toList] using heF) hp⟩

theorem HoldsFactor.mono_frontier {descAddr : ℕ} {f : FactorTable ℕ ℕ}
    {s₀ s₁ : Memory.State} (h : HoldsFactor descAddr f s₀)
    (hp : PreservesBelow s₀.frontier s₀ s₁) : HoldsFactor descAddr f s₁ :=
  h.mono h.1 h.2.2.2.1.1 (by simpa [Array.length_toList] using h.2.2.2.2.1) hp

/-- Contiguous array of 4-word descriptors for `fs` starting at `base`. -/
@[expose] def HoldsFactorList : ℕ → List (FactorTable ℕ ℕ) → Memory.State → Prop
  | base, [], s => base ≤ s.frontier
  | base, f :: fs, s => HoldsFactor base f s ∧ HoldsFactorList (base + 4) fs s

theorem HoldsFactorList.bound {base : ℕ} {fs : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (h : HoldsFactorList base fs s) : base + 4 * fs.length ≤ s.frontier := by
  induction fs generalizing base with
  | nil => simpa [HoldsFactorList] using h
  | cons f rest ih =>
    have hb := ih h.2
    simp only [List.length_cons]
    omega

theorem HoldsFactorList.mono_frontier {base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s₀ s₁ : Memory.State} (h : HoldsFactorList base fs s₀)
    (hp : PreservesBelow s₀.frontier s₀ s₁) : HoldsFactorList base fs s₁ := by
  induction fs generalizing base with
  | nil => exact h.trans hp.2.1
  | cons f rest ih => exact ⟨h.1.mono_frontier hp, ih h.2⟩

/-! ### Primitive 1: Linear membership scan (`memScan`) -/

private structure ScanState where
  cur : ℕ
  found : ℕ

private def ScanState.equiv : ScanState ≃ ℕ × ℕ where
  toFun s := (s.cur, s.found)
  invFun := fun (cur, found) => ⟨cur, found⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ScanState := .ofEquiv ScanState.equiv

/-- Arguments `(ptr, len, key)` for `memScan` and `filterNe`. -/
structure MemScanArgs where
  /-- Field `target` of `MemScanArgs`. -/
  target : ℕ
  /-- Field `base` of `MemScanArgs`. -/
  base : ℕ
  /-- Field `len` of `MemScanArgs`. -/
  len : ℕ

/-- Product equivalence encoding `MemScanArgs` as words. -/
@[expose] def MemScanArgs.equiv : MemScanArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.target, a.base), a.len)
  invFun := fun ((target, base), len) => ⟨target, base, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding MemScanArgs := .ofEquiv MemScanArgs.equiv

private def memScanStep (env : ℕ × ScanState) : Memory.Prog ScanState := do
  let v ← Memory.read env.2.cur
  pure ⟨env.2.cur + 1, if v = env.1 then 1 else env.2.found⟩

/-- Linear scan returning `1` iff `key` occurs in the slice `[ptr, ptr + len)`. -/
def memScan (args : MemScanArgs) : Memory.Prog ℕ := do
  let res ← iterate memScanStep args.target args.len ⟨args.base, 0⟩
  pure res.found

theorem memScan_state (args : MemScanArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (memScan args) = s := by
  unfold memScan
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of memScanStep args.target (fun _ _ => rfl) args.len ⟨args.base, 0⟩ s

theorem memScan_cost (args : MemScanArgs) (s : Memory.State) :
    memoryCost (memScan args) s ≤ args.len := by
  unfold memScan
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  simpa using memoryCost_iterate_le_of memScanStep 1 args.target (fun _ _ => le_rfl)
    args.len ⟨args.base, 0⟩ s

theorem memScan_valid {w : ℕ} (args : MemScanArgs) {s : Memory.State}
    (hb : args.base + args.len ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (memScan args)) := by
  unfold memScan
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  suffices ∀ len cur, cur + len ≤ s.frontier → ∀ found,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate memScanStep args.target len ⟨cur, found⟩)) from
    this args.len args.base hb 0
  intro len
  induction len with
  | zero => intro _ _ _; exact validHistory_pure w s _
  | succ len ih =>
    intro cur hcur found
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (memScanStep (args.target, ⟨cur, found⟩) >>= iterate memScanStep args.target len))
    have hlt : cur < s.frontier := by omega
    refine validHistory_bind_step (validHistory_read_bind hlt (validHistory_pure w s _)) ?_
    exact ih (cur + 1) (by omega) _

theorem memScan_result {args : MemScanArgs} {xs : List ℕ} {s : Memory.State}
    (hxs : Block.HoldsList args.base xs s.mem) (hlen : xs.length = args.len) :
    (Memory.spec 0).clientResult s (memScan args) = if args.target ∈ xs then 1 else 0 := by
  unfold memScan
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ (ys : List ℕ) (cur found : ℕ), Block.HoldsList cur ys s.mem →
      ((Memory.spec 0).clientResult s
        (iterate memScanStep args.target ys.length ⟨cur, found⟩)).found =
      if args.target ∈ ys then 1 else found by
    rw [← hlen]
    exact this xs args.base 0 hxs
  intro ys
  induction ys with
  | nil => intro cur found _; rfl
  | cons u rest ih =>
    intro cur found hcur
    obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hcur
    change ((Memory.spec 0).clientResult s
      (memScanStep (args.target, ⟨cur, found⟩) >>=
        iterate memScanStep args.target rest.length)).found = _
    rw [StateTransitionSpec.clientResult_bind]
    have hstep_st : (Memory.spec 0).clientState s (memScanStep (args.target, ⟨cur, found⟩)) = s :=
      rfl
    have hstep_res : (Memory.spec 0).clientResult s (memScanStep (args.target, ⟨cur, found⟩)) =
        ⟨cur + 1, if u = args.target then 1 else found⟩ := by
      rw [← hhead]; rfl
    rw [hstep_st, hstep_res, ih (cur + 1) _ htail]
    by_cases heq : args.target = u
    · subst heq; simp
    · simp [heq, Ne.symm heq]

theorem memScan_realizes :
    Realizes .exact memScan WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w (args.base + args.len)) (fun _ _ => 0) := by
  unfold memScan
  realize
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st _ => st.cur + j = d.base + d.len) (fun j st t hinv => ?_)
    (show (⟨d.base, 0⟩ : ScanState).cur + d.len = d.base + d.len from rfl)
  dsimp only
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact ⟨h.2.of_le (by omega), h.1⟩
    · exact h.2.of_le (by omega)
  · change (st.cur + 1) + j = d.base + d.len
    omega

/-! ### Descriptor writer (`writeDesc`), live partitioning (`partitionLive`), and `buildOutScope` -/

theorem HoldsFactor.frame_outside {descAddr : ℕ} {f : FactorTable ℕ ℕ} {F : ℕ}
    {s₀ s₁ : Memory.State} (hf : HoldsFactor descAddr f s₀)
    (hsF : s₀.mem descAddr + f.scope.length ≤ F)
    (heF : s₀.mem (descAddr + 2) + f.entries.size ≤ F)
    (hpres : PreservesBelow F s₀ s₁)
    (hdesc : ∀ a, descAddr ≤ a → a < descAddr + 4 → s₁.mem a = s₀.mem a) :
    HoldsFactor descAddr f s₁ := by
  obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
  unfold HoldsFactor
  rw [hdesc descAddr le_rfl (by omega), hdesc (descAddr + 1) (by omega) (by omega),
    hdesc (descAddr + 2) (by omega) (by omega), hdesc (descAddr + 3) (by omega) (by omega)]
  exact ⟨hd.trans hpres.2.1, hsl, hel, hsc.mono hsF hpres,
    hent.mono (by simpa [Array.length_toList] using heF) hpres⟩

/-- Every scope/entry cell referenced by descriptors `fs` lies strictly below `F`. -/
@[expose] def AllDataBelow (F : ℕ) : ℕ → List (FactorTable ℕ ℕ) → Memory.State → Prop
  | _, [], _ => True
  | base, f :: fs, s =>
    s.mem base + f.scope.length ≤ F ∧
    s.mem (base + 2) + f.entries.size ≤ F ∧
    AllDataBelow F (base + 4) fs s

theorem AllDataBelow.of_holdsFactorList {base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (h : HoldsFactorList base fs s) :
    AllDataBelow s.frontier base fs s := by
  induction fs generalizing base with
  | nil => trivial
  | cons f rest ih =>
    exact ⟨h.1.2.2.2.1.1, by simpa [Array.length_toList] using h.1.2.2.2.2.1, ih h.2⟩

theorem AllDataBelow.mono_bound {F₁ F₂ base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (h : AllDataBelow F₁ base fs s) (hle : F₁ ≤ F₂) :
    AllDataBelow F₂ base fs s := by
  induction fs generalizing base with
  | nil => trivial
  | cons f rest ih => exact ⟨h.1.trans hle, h.2.1.trans hle, ih h.2.2⟩

theorem AllDataBelow.frame {F base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s₀ s₁ : Memory.State} (h : AllDataBelow F base fs s₀)
    (hdesc : ∀ a, base ≤ a → a < base + 4 * fs.length → s₁.mem a = s₀.mem a) :
    AllDataBelow F base fs s₁ := by
  induction fs generalizing base with
  | nil => trivial
  | cons f rest ih =>
    simp only [List.length_cons] at hdesc
    refine ⟨?_, ?_, ih h.2.2 fun a hlo hhi => hdesc a (by omega) (by omega)⟩
    · rw [hdesc base le_rfl (by omega)]; exact h.1
    · rw [hdesc (base + 2) (by omega) (by omega)]; exact h.2.1

theorem HoldsFactorList.frame_outside {F base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s₀ s₁ : Memory.State} (h : HoldsFactorList base fs s₀)
    (hdata : AllDataBelow F base fs s₀) (hpres : PreservesBelow F s₀ s₁)
    (hdesc : ∀ a, base ≤ a → a < base + 4 * fs.length → s₁.mem a = s₀.mem a) :
    HoldsFactorList base fs s₁ := by
  induction fs generalizing base with
  | nil => exact h.trans hpres.2.1
  | cons f rest ih =>
    simp only [List.length_cons] at hdesc
    exact ⟨h.1.frame_outside hdata.1 hdata.2.1 hpres
        (fun a hlo hhi => hdesc a hlo (by omega)),
      ih h.2 hdata.2.2 fun a hlo hhi => hdesc a (by omega) (by omega)⟩

theorem holdsFactorList_append {base : ℕ} {fs gs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} :
    HoldsFactorList base (fs ++ gs) s ↔
      HoldsFactorList base fs s ∧ HoldsFactorList (base + 4 * fs.length) gs s := by
  induction fs generalizing base with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨fun h => ⟨(Nat.le_add_right _ _).trans h.bound, h⟩, fun h => h.2⟩
  | cons f rest ih =>
    simp only [List.cons_append, HoldsFactorList, List.length_cons]
    have heq : base + 4 + 4 * rest.length = base + 4 * (rest.length + 1) := by ring
    rw [ih, heq]
    exact and_assoc.symm

theorem allDataBelow_append {F base : ℕ} {fs gs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} :
    AllDataBelow F base (fs ++ gs) s ↔
      AllDataBelow F base fs s ∧ AllDataBelow F (base + 4 * fs.length) gs s := by
  induction fs generalizing base with
  | nil => simp [AllDataBelow]
  | cons f rest ih =>
    simp only [List.cons_append, AllDataBelow, List.length_cons]
    have heq : base + 4 + 4 * rest.length = base + 4 * (rest.length + 1) := by ring
    rw [ih, heq]
    tauto

/-- Arguments for storing one 4-word factor descriptor at `dst`. -/
structure WriteDescArgs where
  /-- Field `dst` of `WriteDescArgs`. -/
  dst : ℕ
  /-- Field `scPtr` of `WriteDescArgs`. -/
  scPtr : ℕ
  /-- Field `scLen` of `WriteDescArgs`. -/
  scLen : ℕ
  /-- Field `enPtr` of `WriteDescArgs`. -/
  enPtr : ℕ
  /-- Field `enLen` of `WriteDescArgs`. -/
  enLen : ℕ

/-- Product equivalence encoding `WriteDescArgs` as words. -/
@[expose] def WriteDescArgs.equiv : WriteDescArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((s.dst, s.scPtr), s.scLen), s.enPtr), s.enLen)
  invFun := fun ((((dst, scPtr), scLen), enPtr), enLen) => ⟨dst, scPtr, scLen, enPtr, enLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding WriteDescArgs := .ofEquiv WriteDescArgs.equiv

/-- Write a 4-word factor descriptor `(scPtr, scLen, enPtr, enLen)` at `dst`. -/
@[expose] def writeDesc (args : WriteDescArgs) : Memory.Prog Unit :=
  Memory.write args.dst args.scPtr >>= fun _ =>
  Memory.write (args.dst + 1) args.scLen >>= fun _ =>
  Memory.write (args.dst + 2) args.enPtr >>= fun _ =>
  Memory.write (args.dst + 3) args.enLen

theorem writeDesc_cost (args : WriteDescArgs) (s : Memory.State) :
    memoryCost (writeDesc args) s = 4 := by
  unfold writeDesc; rfl

theorem writeDesc_valid {w : ℕ} (args : WriteDescArgs) {s : Memory.State}
    (hdst : args.dst + 4 ≤ s.frontier)
    (hf0 : Fits w args.scPtr) (hf1 : Fits w args.scLen)
    (hf2 : Fits w args.enPtr) (hf3 : Fits w args.enLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeDesc args)) := by
  unfold writeDesc
  refine validHistory_write_bind (by omega) hf0 ?_
  refine validHistory_write_bind (by dsimp only; omega) hf1 ?_
  refine validHistory_write_bind (by dsimp only; omega) hf2 ?_
  exact validHistory_write (by dsimp only; omega) hf3

theorem writeDesc_frame (args : WriteDescArgs) (t : Memory.State) :
    ((Memory.spec 0).clientState t (writeDesc args)).frontier = t.frontier ∧
    ∀ a, a < args.dst ∨ args.dst + 4 ≤ a →
      ((Memory.spec 0).clientState t (writeDesc args)).mem a = t.mem a := by
  refine ⟨rfl, fun a ha => ?_⟩
  change Function.update (Function.update (Function.update (Function.update t.mem
    args.dst args.scPtr) (args.dst + 1) args.scLen) (args.dst + 2) args.enPtr)
    (args.dst + 3) args.enLen a = t.mem a
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem writeDesc_spec {w : ℕ} (args : WriteDescArgs) {f : FactorTable ℕ ℕ} {F : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hFdst : F ≤ args.dst) (hdst : args.dst + 4 ≤ s.frontier)
    (hscF : args.scPtr + f.scope.length ≤ F)
    (henF : args.enPtr + f.entries.size ≤ F)
    (hsc_len : args.scLen = f.scope.length) (hen_len : args.enLen = f.entries.size)
    (hsc : HoldsIn args.scPtr f.scope s) (hen : HoldsIn args.enPtr f.entries.toList s) :
    let s' := (Memory.spec 0).clientState s (writeDesc args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeDesc args)) ∧
      s'.frontier = s.frontier ∧
      Memory.WellFormed w s' ∧
      PreservesBelow F s s' ∧
      (∀ a, a < args.dst ∨ args.dst + 4 ≤ a → s'.mem a = s.mem a) ∧
      HoldsFactor args.dst f s' ∧
      s'.mem args.dst = args.scPtr ∧
      s'.mem (args.dst + 2) = args.enPtr := by
  intro s'
  have hv := writeDesc_valid args hdst (hwf.frontier_fits.of_le (by omega))
    (hwf.frontier_fits.of_le (by omega)) (hwf.frontier_fits.of_le (by omega))
    (hwf.frontier_fits.of_le (by omega))
  obtain ⟨hfr, hout⟩ := writeDesc_frame args s
  have hpres : PreservesBelow F s s' :=
    ⟨by omega, hfr.ge, fun a ha => hout a (Or.inl (lt_of_lt_of_le ha hFdst))⟩
  have hst : s'.mem = Function.update (Function.update (Function.update (Function.update s.mem
      args.dst args.scPtr) (args.dst + 1) args.scLen) (args.dst + 2) args.enPtr)
      (args.dst + 3) args.enLen := rfl
  obtain ⟨hm0, hm1, hm2, hm3⟩ : s'.mem args.dst = args.scPtr ∧
      s'.mem (args.dst + 1) = args.scLen ∧ s'.mem (args.dst + 2) = args.enPtr ∧
      s'.mem (args.dst + 3) = args.enLen := by
    simp [hst]
  refine ⟨hv, hfr, wellFormed_clientState hwf hv, hpres, hout, ?_, hm0, hm2⟩
  unfold HoldsFactor
  rw [hm0, hm1, hm2, hm3]
  exact ⟨hfr ▸ hdst, hsc_len, hen_len, hsc.mono hscF hpres,
    hen.mono (by simpa [Array.length_toList] using henF) hpres⟩

theorem writeDesc_realizes :
    Realizes .exact writeDesc WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w (args.dst + 3)) (fun _ _ => 0) := by
  unfold writeDesc
  realize
  · exact h.of_le (by omega)
  · exact h.of_le (by omega)
  · exact h

end Cslib.Algorithms.WordRAM.VariableElimination
