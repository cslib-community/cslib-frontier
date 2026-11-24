/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.CSP.VariableElimination
public import CslibFrontier.Computability.WordRAM.ListArray
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Tactic.Realize

/-!
# Integer Power (`powProg`) and Mixed-Radix Lookup (`lookupAssign`)

Realizable exact-basis Word-RAM routines for computing `d ^ n` and extracting the assigned value of
a variable from an LSB mixed-radix index over an array scope.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.powProg`: repeated multiplication computing `d ^ n`.
* `Cslib.Algorithms.WordRAM.VariableElimination.lookupAssign`: radix assignment value lookup.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Primitive 3: Power `d ^ n`, radix assignment lookup, and scope evaluation -/

/-- Arguments `(base, exp)` for `powProg`. -/
structure PowArgs where
  /-- Field `base` of `PowArgs`. -/
  base : ℕ
  /-- Field `exp` of `PowArgs`. -/
  exp : ℕ

/-- Product equivalence encoding `PowArgs` as words. -/
@[expose] def PowArgs.equiv : PowArgs ≃ ℕ × ℕ where
  toFun a := (a.base, a.exp)
  invFun := fun (base, exp) => ⟨base, exp⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding PowArgs := .ofEquiv PowArgs.equiv

private def powStep (env : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  pure (env.2 * env.1)

/-- Exact-basis Word-RAM program computing `base ^ exp`. -/
def powProg (args : PowArgs) : Memory.Prog ℕ :=
  iterate powStep args.base args.exp 1

theorem powProg_state (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (powProg args) = s :=
  clientState_iterate_eq_of powStep args.base (fun _ _ => rfl) args.exp 1 s

theorem powProg_cost (args : PowArgs) (s : Memory.State) :
    memoryCost (powProg args) s ≤ args.exp := by
  unfold powProg
  simpa using memoryCost_iterate_le_of powStep 1 args.base (fun _ _ => le_rfl) args.exp 1 s

theorem powProg_valid {w : ℕ} (args : PowArgs) {s : Memory.State} (hs : 0 < s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (powProg args)) :=
  validHistory_iterate_inv (fun t => 0 < t.frontier) powStep args.base
    (fun _ t ht => validHistory_read_bind ht (validHistory_pure w t _)) args.exp 1 hs

theorem powProg_result (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientResult s (powProg args) = args.base ^ args.exp := by
  unfold powProg
  suffices ∀ n acc, (Memory.spec 0).clientResult s (iterate powStep args.base n acc) =
      acc * args.base ^ n by
    simpa using this args.exp 1
  intro n
  induction n with
  | zero =>
    intro acc
    change acc = acc * args.base ^ 0
    simp
  | succ n ih =>
    intro acc
    change (Memory.spec 0).clientResult s
      (powStep (args.base, acc) >>= iterate powStep args.base n) = _
    rw [StateTransitionSpec.clientResult_bind]
    have hst : (Memory.spec 0).clientState s (powStep (args.base, acc)) = s := rfl
    have hres : (Memory.spec 0).clientResult s (powStep (args.base, acc)) = acc * args.base := rfl
    rw [hst, hres, ih (acc * args.base), pow_succ', Nat.mul_assoc]

theorem powProg_realizes :
    Realizes .exact powProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w ((max 1 args.base) ^ args.exp)) (fun _ _ => 0) := by
  unfold powProg
  realize
  · exact h.1
  · refine iterationSafe_of_stepInv _ _ w d
      (fun j acc _ => acc * (max 1 d.base) ^ j ≤ (max 1 d.base) ^ d.exp)
      (fun j acc t hinv => ?_) (Nat.one_mul _).le
    have hm : acc * d.base ≤ acc * max 1 d.base := Nat.mul_le_mul_left acc (le_max_right 1 d.base)
    have h1 : 1 ≤ (max 1 d.base) ^ j := Nat.one_le_pow j _ (le_max_left 1 d.base)
    have hle : acc * d.base ≤ (max 1 d.base) ^ d.exp := by
      calc acc * d.base ≤ acc * max 1 d.base := hm
        _ ≤ (acc * max 1 d.base) * (max 1 d.base) ^ j := Nat.le_mul_of_pos_right _ h1
        _ = acc * (max 1 d.base) ^ (j + 1) := by rw [pow_succ', Nat.mul_assoc]
        _ ≤ (max 1 d.base) ^ d.exp := hinv
    refine ⟨h.2.of_le hle, ?_⟩
    change (acc * d.base) * (max 1 d.base) ^ j ≤ (max 1 d.base) ^ d.exp
    calc (acc * d.base) * (max 1 d.base) ^ j
        ≤ (acc * max 1 d.base) * (max 1 d.base) ^ j := Nat.mul_le_mul_right _ hm
      _ = acc * (max 1 d.base) ^ (j + 1) := by rw [pow_succ', Nat.mul_assoc]
      _ ≤ (max 1 d.base) ^ d.exp := hinv

/-- Arguments for reading the value of variable `v` in a mixed-radix assignment. -/
structure LookupArgs where
  /-- Field `dom` of `LookupArgs`. -/
  dom : ℕ
  /-- Field `target` of `LookupArgs`. -/
  target : ℕ
  /-- Field `outPtr` of `LookupArgs`. -/
  outPtr : ℕ
  /-- Field `outLen` of `LookupArgs`. -/
  outLen : ℕ
  /-- Field `idx` of `LookupArgs`. -/
  idx : ℕ

/-- Product equivalence encoding `LookupArgs` as words. -/
@[expose] def LookupArgs.equiv : LookupArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.dom, a.target), a.outPtr), a.outLen), a.idx)
  invFun := fun ((((dom, target), outPtr), outLen), idx) => ⟨dom, target, outPtr, outLen, idx⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding LookupArgs := .ofEquiv LookupArgs.equiv

private structure LookupEnv where
  dom : ℕ
  target : ℕ

private def LookupEnv.equiv : LookupEnv ≃ ℕ × ℕ where
  toFun e := (e.dom, e.target)
  invFun := fun (dom, target) => ⟨dom, target⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupEnv := .ofEquiv LookupEnv.equiv

private structure LookupState where
  cur : ℕ
  remIdx : ℕ
  found : ℕ
  ans : ℕ

private def LookupState.equiv : LookupState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.cur, s.remIdx), s.found), s.ans)
  invFun := fun (((cur, remIdx), found), ans) => ⟨cur, remIdx, found, ans⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupState := .ofEquiv LookupState.equiv

private def lookupStep (p : LookupEnv × LookupState) : Memory.Prog LookupState := do
  let u ← Memory.read p.2.cur
  let dig := p.2.remIdx % p.1.dom
  let nextIdx := p.2.remIdx / p.1.dom
  if p.2.found = 0 ∧ u = p.1.target then
    pure ⟨p.2.cur + 1, nextIdx, 1, dig⟩
  else
    pure ⟨p.2.cur + 1, nextIdx, p.2.found, p.2.ans⟩

/-- Look up variable `v` in an LSB-encoded radix-`dom` assignment. -/
def lookupAssign (args : LookupArgs) : Memory.Prog ℕ := do
  let res ← iterate lookupStep ⟨args.dom, args.target⟩ args.outLen ⟨args.outPtr, args.idx, 0, 0⟩
  pure res.ans

theorem lookupAssign_state (args : LookupArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (lookupAssign args) = s := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of lookupStep ⟨args.dom, args.target⟩
    (fun a t => by
      unfold lookupStep
      change (Memory.spec 0).clientState t
        (if a.found = 0 ∧ t.mem a.cur = args.target then _ else _) = t
      split_ifs <;> rfl)
    args.outLen ⟨args.outPtr, args.idx, 0, 0⟩ s

theorem lookupAssign_cost (args : LookupArgs) (s : Memory.State) :
    memoryCost (lookupAssign args) s ≤ args.outLen := by
  unfold lookupAssign
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  simpa using memoryCost_iterate_le_of lookupStep 1 ⟨args.dom, args.target⟩
    (fun a t => by
      unfold lookupStep
      rw [memoryCost_bind', memoryCost_read]
      dsimp only
      rw [memoryCost_ite]
      split_ifs <;> simp)
    args.outLen ⟨args.outPtr, args.idx, 0, 0⟩ s

theorem lookupAssign_valid {w : ℕ} (args : LookupArgs) {s : Memory.State}
    (hb : args.outPtr + args.outLen ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (lookupAssign args)) := by
  unfold lookupAssign
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  suffices ∀ len cur, cur + len ≤ s.frontier → ∀ remIdx found ans,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate lookupStep ⟨args.dom, args.target⟩ len ⟨cur, remIdx, found, ans⟩)) from
    this args.outLen args.outPtr hb args.idx 0 0
  intro len
  induction len with
  | zero => intro _ _ _ _ _; exact validHistory_pure w s _
  | succ len ih =>
    intro cur hcur remIdx found ans
    have hlt : cur < s.frontier := by omega
    have hstep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩))) := by
      refine validHistory_read_bind hlt ?_
      split_ifs <;> exact validHistory_pure w s _
    have hst : (Memory.spec 0).clientState s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩)) = s := by
      unfold lookupStep
      change (Memory.spec 0).clientState s
        (if found = 0 ∧ s.mem cur = args.target then _ else _) = s
      split_ifs <;> rfl
    have hcur_next : ((Memory.spec 0).clientResult s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩))).cur = cur + 1 := by
      unfold lookupStep
      have : ((Memory.spec 0).clientResult s
          (if found = 0 ∧ s.mem cur = args.target then
            (pure ⟨cur + 1, remIdx / args.dom, 1, remIdx % args.dom⟩ : Memory.Prog LookupState)
           else
            pure ⟨cur + 1, remIdx / args.dom, found, ans⟩)).cur = cur + 1 := by
        split_ifs <;> rfl
      exact this
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩) >>=
          iterate lookupStep ⟨args.dom, args.target⟩ len))
    refine validHistory_bind_step hstep ?_
    rw [hst]
    let r := (Memory.spec 0).clientResult s
      (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩))
    exact ih r.cur (by rw [hcur_next]; omega) r.remIdx r.found r.ans

theorem lookupAssign_result {args : LookupArgs} {us : List ℕ} {s : Memory.State}
    (hus : Block.HoldsList args.outPtr us s.mem) (hlen : us.length = args.outLen) :
    (Memory.spec 0).clientResult s (lookupAssign args) =
      assignScope us (lsbDecode args.dom us.length args.idx) args.target := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientResult_bind, ← hlen]
  have hfound1 : ∀ (n cur remIdx ans : ℕ),
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ n ⟨cur, remIdx, 1, ans⟩)).ans = ans := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro cur remIdx ans
      change ((Memory.spec 0).clientResult s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 1, ans⟩) >>=
          iterate lookupStep ⟨args.dom, args.target⟩ n)).ans = ans
      rw [StateTransitionSpec.clientResult_bind]
      have hst : (Memory.spec 0).clientState s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 1, ans⟩)) = s := rfl
      have hres : (Memory.spec 0).clientResult s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 1, ans⟩)) =
          ⟨cur + 1, remIdx / args.dom, 1, ans⟩ := rfl
      rw [hst, hres]
      exact ih _ _ _
  suffices ∀ (zs : List ℕ) (cur remIdx : ℕ), Block.HoldsList cur zs s.mem →
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ zs.length ⟨cur, remIdx, 0, 0⟩)).ans =
      assignScope zs (lsbDecode args.dom zs.length remIdx) args.target from
    this us args.outPtr args.idx hus
  intro zs
  induction zs with
  | nil => intro cur remIdx _; rfl
  | cons u rest ih =>
    intro cur remIdx hcur
    obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hcur
    change ((Memory.spec 0).clientResult s
      (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩) >>=
        iterate lookupStep ⟨args.dom, args.target⟩ rest.length)).ans = _
    rw [StateTransitionSpec.clientResult_bind]
    by_cases htu : args.target = u
    · have hst : (Memory.spec 0).clientState s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩)) = s := by
        unfold lookupStep
        change (Memory.spec 0).clientState s
          (if 0 = 0 ∧ s.mem cur = args.target then _ else _) = s
        rw [hhead, ite_eq_left ⟨rfl, htu.symm⟩]; rfl
      have hres : (Memory.spec 0).clientResult s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩)) =
          ⟨cur + 1, remIdx / args.dom, 1, remIdx % args.dom⟩ := by
        unfold lookupStep
        change (Memory.spec 0).clientResult s
          (if 0 = 0 ∧ s.mem cur = args.target then _ else _) = _
        rw [hhead, ite_eq_left ⟨rfl, htu.symm⟩]; rfl
      rw [hst, hres, hfound1]
      simp [lsbDecode, assignScope, htu]
    · have hne : u ≠ args.target := Ne.symm htu
      have hst : (Memory.spec 0).clientState s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩)) = s := by
        unfold lookupStep
        change (Memory.spec 0).clientState s
          (if 0 = 0 ∧ s.mem cur = args.target then _ else _) = s
        rw [hhead, ite_eq_right (fun h => hne h.2)]; rfl
      have hres : (Memory.spec 0).clientResult s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩)) =
          ⟨cur + 1, remIdx / args.dom, 0, 0⟩ := by
        unfold lookupStep
        change (Memory.spec 0).clientResult s
          (if 0 = 0 ∧ s.mem cur = args.target then _ else _) = _
        rw [hhead, ite_eq_right (fun h => hne h.2)]; rfl
      rw [hst, hres, ih (cur + 1) (remIdx / args.dom) htail]
      simp [lsbDecode, assignScope, htu]

theorem lookupAssign_realizes :
    Realizes .exact lookupAssign WordEncoding.encode WordEncoding.encode
      (fun w args _ => 0 < args.dom ∧ Fits w 1 ∧ Fits w (args.outPtr + args.outLen))
      (fun _ _ => 0) := by
  unfold lookupAssign
  realize
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st _ => st.cur + j = d.outPtr + d.outLen)
    (fun j st t hinv => ?_)
    (show (⟨d.outPtr, d.idx, 0, 0⟩ : LookupState).cur + d.outLen = d.outPtr + d.outLen from rfl)
  dsimp only
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact ⟨Nat.ne_of_gt h.1, h.2.2.of_le (by omega), h.2.1⟩
    · exact ⟨Nat.ne_of_gt h.1, h.2.2.of_le (by omega)⟩
    · exact ⟨Nat.ne_of_gt h.1, h.2.2.of_le (by omega)⟩
  · unfold lookupStep
    have : ((Memory.spec 0).clientResult t
        (if st.found = 0 ∧ t.mem st.cur = d.target then
          (pure ⟨st.cur + 1, st.remIdx / d.dom, 1, st.remIdx % d.dom⟩ : Memory.Prog LookupState)
         else
          pure ⟨st.cur + 1, st.remIdx / d.dom, st.found, st.ans⟩)).cur + j =
        d.outPtr + d.outLen := by
      split_ifs
      · change (st.cur + 1) + j = d.outPtr + d.outLen; omega
      · change (st.cur + 1) + j = d.outPtr + d.outLen; omega
    exact this

theorem lookupAssign_lt {args : LookupArgs} (hd : 0 < args.dom) (s : Memory.State) :
    (Memory.spec 0).clientResult s (lookupAssign args) < args.dom := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ (n cur remIdx found ans : ℕ), ans < args.dom →
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ n ⟨cur, remIdx, found, ans⟩)).ans <
      args.dom from
    this args.outLen args.outPtr args.idx 0 0 hd
  intro n
  induction n with
  | zero => intro _ _ _ _ hans; exact hans
  | succ n ih =>
    intro cur remIdx found ans hans
    change ((Memory.spec 0).clientResult s
      (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩) >>=
        iterate lookupStep ⟨args.dom, args.target⟩ n)).ans < args.dom
    rw [StateTransitionSpec.clientResult_bind]
    have hst : (Memory.spec 0).clientState s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩)) = s := by
      unfold lookupStep
      change (Memory.spec 0).clientState s
        (if found = 0 ∧ s.mem cur = args.target then _ else _) = s
      split_ifs <;> rfl
    have hnext : ((Memory.spec 0).clientResult s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩))).ans < args.dom := by
      unfold lookupStep
      have : ((Memory.spec 0).clientResult s
          (if found = 0 ∧ s.mem cur = args.target then
            (pure ⟨cur + 1, remIdx / args.dom, 1, remIdx % args.dom⟩ : Memory.Prog LookupState)
           else
            pure ⟨cur + 1, remIdx / args.dom, found, ans⟩)).ans < args.dom := by
        split_ifs
        · exact Nat.mod_lt _ hd
        · exact hans
      exact this
    rw [hst]
    exact ih _ _ _ _ hnext

end Cslib.Algorithms.WordRAM.VariableElimination
